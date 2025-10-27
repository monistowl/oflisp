// OFLISP Reference VM (Rust) — v0.1
// ------------------------------------------------------------
// Rreference interpreter + bytecode VM for Operating Function LISP
//

use anyhow::{anyhow, Result};
use blake3::Hasher;
use num_bigint::{BigInt, Sign};
use num_traits::{One, ToPrimitive, Zero};
use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display};
use std::rc::Rc;
use unicode_ident::{is_xid_continue, is_xid_start};

// ------------------------- Utilities -------------------------

/// Encode `n` using the unsigned LEB128 length format mandated by
/// `spec/core.md §6` for canonical TLV payload sizing.
fn uleb128_encode(mut n: u128) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let mut byte = (n & 0x7F) as u8;
        n >>= 7;
        if n != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if n == 0 {
            break;
        }
    }
    out
}

/// Decode an unsigned LEB128 integer while reporting how many bytes were
/// consumed, as required for TLV lengths in `spec/core.md §6`.
fn uleb128_decode(mut bytes: &[u8]) -> Result<(u128, usize)> {
    let mut result: u128 = 0;
    let mut shift = 0u32;
    let mut used = 0usize;
    loop {
        if bytes.is_empty() {
            return Err(anyhow!("ULEB128: unexpected EOF"));
        }
        let b = bytes[0];
        bytes = &bytes[1..];
        used += 1;
        result |= ((b & 0x7F) as u128) << shift;
        if (b & 0x80) == 0 {
            break;
        }
        shift += 7;
        if shift > 126 {
            return Err(anyhow!("ULEB128: too large"));
        }
    }
    Ok((result, used))
}

/// Convert a `BigInt` into the minimal big-endian two's complement payload
/// described in `spec/core.md §6.2`.
fn be_twos_complement_from_bigint(n: &BigInt) -> Vec<u8> {
    // Minimal-width big-endian two's complement, with zero as 0x00.
    if n.is_zero() {
        return vec![0u8];
    }
    let (sign, mut mag) = n.to_bytes_be();
    match sign {
        Sign::Plus => {
            // Ensure the top bit is 0 (positive), minimal length
            if mag[0] & 0x80 != 0 {
                mag.insert(0, 0x00);
            }
            // Strip redundant leading 0x00
            while mag.len() > 1 && mag[0] == 0x00 && (mag[1] & 0x80) == 0 {
                mag.remove(0);
            }
            mag
        }
        Sign::Minus => {
            // Represent magnitude as two's complement negative.
            // Algorithm: form minimal positive width, then two's complement.
            if mag[0] & 0x80 == 0 {
                mag.insert(0, 0x00);
            }
            // Invert
            for b in mag.iter_mut() {
                *b = !*b;
            }
            // Add 1
            let mut carry = 1u16;
            for i in (0..mag.len()).rev() {
                let v = (mag[i] as u16) + carry;
                mag[i] = (v & 0xFF) as u8;
                carry = v >> 8;
            }
            // Ensure leading 0xFF and minimal
            if mag[0] != 0xFF {
                mag.insert(0, 0xFF);
            }
            while mag.len() > 1 && mag[0] == 0xFF && (mag[1] & 0x80) != 0 {
                mag.remove(0);
            }
            mag
        }
        Sign::NoSign => vec![0],
    }
}

/// Reconstruct a `BigInt` from the canonical two's complement payload
/// described in `spec/core.md §6.2`.
fn be_twos_complement_to_bigint(bytes: &[u8]) -> BigInt {
    if bytes.is_empty() {
        return BigInt::zero();
    }
    let neg = (bytes[0] & 0x80) != 0;
    if !neg {
        BigInt::from_bytes_be(Sign::Plus, bytes)
    } else {
        // Two's complement negative: invert and add 1, then negate
        let mut inv = bytes.to_vec();
        for b in inv.iter_mut() {
            *b = !*b;
        }
        // add 1
        let mut carry = 1u16;
        for i in (0..inv.len()).rev() {
            let v = (inv[i] as u16) + carry;
            inv[i] = (v & 0xFF) as u8;
            carry = v >> 8;
        }
        let mag = BigInt::from_bytes_be(Sign::Plus, &inv);
        -mag
    }
}

// ------------------------- Values ---------------------------

/// Interned symbol identity as defined in `spec/core.md §3.1`.
#[derive(Clone)]
pub struct Symbol {
    pub package: String,
    pub name: String,
    pub id: [u8; 32],
}

impl Symbol {
    /// Create a symbol and derive its hash id per `spec/core.md §3.1`/§6.4.
    pub fn new(package: impl Into<String>, name: impl Into<String>) -> Self {
        let package = package.into();
        let name = name.into();
        let mut h = Hasher::new();
        h.update(package.as_bytes());
        h.update(&[0x00]);
        h.update(name.as_bytes());
        let mut id = [0u8; 32];
        id.copy_from_slice(h.finalize().as_bytes());
        Self { package, name, id }
    }
}

impl Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.package, self.name)
    }
}

/// Tagged value universe described in `spec/core.md §3`.
#[derive(Clone)]
pub enum Value {
    Nil,
    Int(BigInt),
    Str(String),
    Sym(Rc<Symbol>),
    Bytes(Vec<u8>),
    Pair(Rc<Value>, Rc<Value>),
    Closure(Rc<Closure>),
    Error(Box<ErrorVal>),
}

/// Structured error triple per `spec/core.md §3.3`.
#[derive(Clone)]
pub struct ErrorVal {
    pub code: Rc<Symbol>,
    pub message: String,
    pub payload: Value,
}

impl Debug for ErrorVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<error {}:{}>", self.code.name, self.message)
    }
}

impl Value {
    /// Interpret `self` using the predicate rules from `spec/core.md §3.2`.
    pub fn truthy(&self) -> bool {
        match self {
            Value::Nil => false,
            Value::Int(n) => !n.is_zero(),
            _ => true,
        }
    }
    /// Convenience to test whether `self` is a spec error value (`spec/core.md §3.3`).
    pub fn is_error(&self) -> bool {
        matches!(self, Value::Error(_))
    }

    /// Produce the canonical external representation required by `spec/core.md §11`.
    pub fn to_canonical(&self) -> String {
        match self {
            Value::Nil => "()".to_string(),
            Value::Int(n) => n.to_string(),
            Value::Str(s) => format!("\"{}\"", escape_canonical_string(s)),
            Value::Sym(sym) => canonical_symbol(sym),
            Value::Bytes(bytes) => {
                let body = bytes
                    .iter()
                    .map(|b| b.to_string())
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("#u8({body})")
            }
            Value::Pair(_, _) => canonical_list(self),
            Value::Closure(c) => format!(
                "#<closure code={} env={}>",
                hex(&c.code_hash),
                hex(&c.env_shape_hash)
            ),
            Value::Error(err) => format!(
                "#<error {}:{}>",
                canonical_symbol(err.code.as_ref()),
                err.message
            ),
        }
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Nil => write!(f, "()"),
            Value::Int(n) => write!(f, "{}", n),
            Value::Str(s) => write!(f, "\"{}\"", s),
            Value::Sym(sy) => write!(f, "{sy:?}"),
            Value::Bytes(b) => write!(
                f,
                "#u8({})",
                b.iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Value::Pair(a, d) => write!(f, "({a:?} . {d:?})"),
            Value::Closure(c) => write!(
                f,
                "#<closure code={} env={}>",
                hex(&c.code_hash),
                hex(&c.env_shape_hash)
            ),
            Value::Error(e) => write!(f, "{e:?}"),
        }
    }
}

/// Apply the escape discipline for canonical printing (`spec/core.md §11`).
fn escape_canonical_string(input: &str) -> String {
    input
        .chars()
        .flat_map(|ch| match ch {
            '"' => ['\\', '"'].into_iter().collect::<Vec<_>>(),
            '\\' => ['\\', '\\'].into_iter().collect(),
            '\n' => ['\\', 'n'].into_iter().collect(),
            '\t' => ['\\', 't'].into_iter().collect(),
            '\r' => ['\\', 'r'].into_iter().collect(),
            ch if (ch as u32) < 0x20 || ch == '\u{7F}' => {
                let mut buf = vec!['\\', 'x'];
                let code = ch as u32;
                buf.push(int_to_hex((code >> 4) as u8));
                buf.push(int_to_hex((code & 0xF) as u8));
                buf
            }
            ch => vec![ch],
        })
        .collect()
}

/// Convert a 4-bit nibble into uppercase hex for canonical escapes (`spec/core.md §11`).
fn int_to_hex(nibble: u8) -> char {
    match nibble {
        0..=9 => (b'0' + nibble) as char,
        10..=15 => (b'A' + (nibble - 10)) as char,
        _ => unreachable!(),
    }
}

/// Render a symbol using the `package/name` rules from `spec/core.md §11`.
fn canonical_symbol(sym: &Symbol) -> String {
    let name = canonical_symbol_component(&sym.name);
    if sym.package == "user" {
        name
    } else {
        let pkg = canonical_symbol_component(&sym.package);
        format!("{pkg}/{name}")
    }
}

/// Escape a symbol component if it contains delimiter characters (`spec/core.md §11`).
fn canonical_symbol_component(component: &str) -> String {
    if requires_symbol_quoting(component) {
        let escaped: String = component
            .chars()
            .flat_map(|ch| match ch {
                '|' => vec!['\\', '|'],
                '\\' => vec!['\\', '\\'],
                ch => vec![ch],
            })
            .collect();
        format!("|{escaped}|")
    } else {
        component.to_string()
    }
}

/// Detect whether a symbol needs `|...|` quoting in canonical output (`spec/core.md §11`).
fn requires_symbol_quoting(component: &str) -> bool {
    component.chars().any(|ch| {
        ch.is_whitespace()
            || matches!(
                ch,
                '(' | ')' | '"' | '\'' | '`' | ',' | '@' | '|' | ';' | '#' | '[' | ']' | '{' | '}'
            )
    })
}

/// Print a list/dotted pair according to `spec/core.md §11`.
fn canonical_list(value: &Value) -> String {
    let mut parts = Vec::new();
    let mut cursor = value;
    loop {
        match cursor {
            Value::Pair(car, cdr) => {
                parts.push(car.to_canonical());
                cursor = cdr.as_ref();
            }
            Value::Nil => {
                return format!("({})", parts.join(" "));
            }
            other => {
                let head = parts.join(" ");
                let tail = other.to_canonical();
                if head.is_empty() {
                    return format!("(. {tail})");
                }
                return format!("({head} . {tail})");
            }
        }
    }
}

// ----------------------------- Reader -----------------------------

/// Helper to produce reader errors per `spec/core.md §2.2/§3.3`.
fn reader_error(message: &str, payload: Value) -> Value {
    Value::Error(Box::new(ErrorVal {
        code: Rc::new(Symbol::new("error", "reader")),
        message: message.to_string(),
        payload,
    }))
}

/// Build a proper list from `items`, preserving reader order (`spec/core.md §2.3`).
fn list_from(items: Vec<Value>) -> Value {
    let mut acc = Value::Nil;
    for item in items.into_iter().rev() {
        acc = Value::Pair(Rc::new(item), Rc::new(acc));
    }
    acc
}

/// Build a two-element list in evaluation order (`spec/core.md §2.3`).
fn list2(a: Value, b: Value) -> Value {
    list_from(vec![a, b])
}

/// Construct a user-package symbol literal per `spec/core.md §2.2`.
fn symbol(name: &str) -> Value {
    Value::Sym(Rc::new(Symbol::new("user", name)))
}

/// Stateful reader implementing the grammar from `spec/core.md §2`.
struct Reader<'a> {
    chars: std::str::Chars<'a>,
    offset: usize,
}

impl<'a> Reader<'a> {
    /// Initialize a reader over raw UTF-8 source (`spec/core.md §2.1`).
    fn new(src: &'a str) -> Self {
        Self {
            chars: src.chars(),
            offset: 0,
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }

    fn peek_n(&self, n: usize) -> Option<char> {
        let mut it = self.chars.clone();
        it.nth(n)
    }

    fn bump(&mut self) -> Option<char> {
        let mut iter = self.chars.clone();
        let ch = iter.next()?;
        self.offset += ch.len_utf8();
        self.chars = iter;
        Some(ch)
    }

    /// Skip whitespace and comments, rejecting carriage returns (`spec/core.md §2.1/§2.2`).
    fn skip_ws(&mut self) -> Result<(), Value> {
        loop {
            let Some(ch) = self.peek() else {
                return Ok(());
            };
            match ch {
                ' ' | '\t' | '\n' => {
                    self.bump();
                }
                ';' => {
                    self.bump();
                    while let Some(next) = self.peek() {
                        if next == '\n' {
                            break;
                        }
                        self.bump();
                    }
                }
                '\r' => {
                    return Err(reader_error(
                        "carriage-return",
                        Value::Int(BigInt::from(self.offset as i64)),
                    ));
                }
                _ => return Ok(()),
            }
        }
    }

    /// Consume the entire stream and return the top-level forms (`spec/core.md §2.3`).
    fn read_all(mut self) -> Result<Vec<Value>, Value> {
        let mut out = Vec::new();
        self.skip_ws()?;
        while self.peek().is_some() {
            if let Some(form) = self.read_form()? {
                out.push(form);
            }
            self.skip_ws()?;
        }
        Ok(out)
    }

    /// Parse a single datum or return `None` at EOF (`spec/core.md §2.3`).
    fn read_form(&mut self) -> Result<Option<Value>, Value> {
        self.skip_ws()?;
        let Some(ch) = self.peek() else {
            return Ok(None);
        };
        match ch {
            '(' => {
                self.bump();
                self.read_list().map(Some)
            }
            ')' => Err(reader_error("unexpected )", Value::Nil)),
            '\'' => {
                self.bump();
                let datum = self.require_form("quote")?;
                Ok(Some(list2(symbol("quote"), datum)))
            }
            '`' => {
                self.bump();
                let datum = self.require_form("quasiquote")?;
                Ok(Some(list2(symbol("quasiquote"), datum)))
            }
            ',' => {
                self.bump();
                if self.peek() == Some('@') {
                    self.bump();
                    let datum = self.require_form("unquote-splicing")?;
                    Ok(Some(list2(symbol("unquote-splicing"), datum)))
                } else {
                    let datum = self.require_form("unquote")?;
                    Ok(Some(list2(symbol("unquote"), datum)))
                }
            }
            '"' => {
                self.bump();
                self.read_string().map(|s| Some(Value::Str(s)))
            }
            '#' => {
                self.bump();
                self.read_dispatch().map(Some)
            }
            _ => {
                if ch == '-' {
                    if let Some(next) = self.peek_n(1) {
                        if next.is_ascii_digit() {
                            return self.read_number().map(Some);
                        }
                    }
                }
                if ch.is_ascii_digit() {
                    return self.read_number().map(Some);
                }
                self.read_symbol().map(Some)
            }
        }
    }

    fn require_form(&mut self, ctx: &str) -> Result<Value, Value> {
        match self.read_form()? {
            Some(v) => Ok(v),
            None => Err(reader_error(&format!("{ctx}: eof"), Value::Nil)),
        }
    }

    fn read_list(&mut self) -> Result<Value, Value> {
        let mut items = Vec::new();
        loop {
            self.skip_ws()?;
            let Some(ch) = self.peek() else {
                return Err(reader_error("list: eof", Value::Nil));
            };
            if ch == ')' {
                self.bump();
                return Ok(list_from(items));
            }
            if ch == '.' {
                if !self.after_dot_delimited() {
                    let sym = self.read_symbol()?;
                    items.push(sym);
                    continue;
                }
                self.bump();
                let tail = self.require_form("dotted tail")?;
                self.skip_ws()?;
                if self.bump() != Some(')') {
                    return Err(reader_error("dotted: missing )", Value::Nil));
                }
                let mut result = tail;
                for item in items.into_iter().rev() {
                    result = Value::Pair(Rc::new(item), Rc::new(result));
                }
                return Ok(result);
            }
            let datum = self
                .read_form()?
                .ok_or_else(|| reader_error("list: eof", Value::Nil))?;
            items.push(datum);
        }
    }

    /// Check that a dotted tail is followed by a delimiter (`spec/core.md §2.3`).
    fn after_dot_delimited(&self) -> bool {
        let mut iter = self.chars.clone();
        iter.next();
        match iter.next() {
            None => true,
            Some(ch) => is_delimiter(ch),
        }
    }

    /// Parse an integer literal using the decimal grammar (`spec/core.md §2.2`).
    fn read_number(&mut self) -> Result<Value, Value> {
        let mut repr = String::new();
        if self.peek() == Some('-') {
            repr.push('-');
            self.bump();
        }
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                repr.push(ch);
                self.bump();
            } else {
                break;
            }
        }
        if repr == "-" {
            return Ok(symbol("-"));
        }
        if repr.is_empty() {
            return Err(reader_error("number", Value::Nil));
        }
        if let Some(ch) = self.peek() {
            if !is_delimiter(ch) {
                return Err(reader_error("number", Value::Str(format!("{repr}{ch}"))));
            }
        }
        let n = BigInt::parse_bytes(repr.as_bytes(), 10)
            .ok_or_else(|| reader_error("number parse", Value::Str(repr.clone())))?;
        Ok(Value::Int(n))
    }

    /// Parse an unquoted symbol token and validate identifier rules (`spec/core.md §2.2`).
    fn read_symbol(&mut self) -> Result<Value, Value> {
        if self.peek() == Some('|') {
            return self.read_quoted_symbol(None);
        }
        let mut token = String::new();
        while let Some(ch) = self.peek() {
            if is_delimiter(ch) {
                break;
            }
            token.push(ch);
            self.bump();
        }
        if token.is_empty() {
            return Err(reader_error("symbol", Value::Nil));
        }
        if token == "()" {
            return Ok(Value::Nil);
        }
        self.symbol_from_token(token)
    }

    /// Split `token` into package/name and validate per `spec/core.md §2.2`.
    fn symbol_from_token(&mut self, token: String) -> Result<Value, Value> {
        if token == "." {
            return Err(reader_error("unexpected .", Value::Nil));
        }
        let (pkg, name) = if let Some(idx) = token.find('/') {
            let (pkg, rest) = token.split_at(idx);
            if rest.len() <= 1 {
                return Err(reader_error("symbol name", Value::Str(token)));
            }
            (pkg.to_string(), rest[1..].to_string())
        } else {
            ("user".to_string(), token)
        };
        if !pkg.is_empty() && pkg != "user" && !valid_symbol_name(&pkg) {
            return Err(reader_error("package", Value::Str(pkg)));
        }
        if !valid_symbol_name(&name) {
            return Err(reader_error("symbol", Value::Str(name)));
        }
        Ok(Value::Sym(Rc::new(Symbol::new(pkg, name))))
    }

    /// Parse `|quoted|` symbol segments and optional explicit package (`spec/core.md §2.2`).
    fn read_quoted_symbol(&mut self, package: Option<String>) -> Result<Value, Value> {
        self.bump();
        let mut buf = String::new();
        loop {
            let Some(ch) = self.bump() else {
                return Err(reader_error("symbol quote eof", Value::Nil));
            };
            match ch {
                '|' => break,
                '\\' => {
                    let esc = self
                        .bump()
                        .ok_or_else(|| reader_error("symbol escape", Value::Nil))?;
                    buf.push(esc);
                }
                other => buf.push(other),
            }
        }
        if let Some(pkg) = package {
            return Ok(Value::Sym(Rc::new(Symbol::new(pkg, buf))));
        }
        if self.peek() == Some('/') {
            self.bump();
            return self.read_quoted_symbol(Some(buf));
        }
        Ok(Value::Sym(Rc::new(Symbol::new("user", buf))))
    }

    /// Parse a string literal, handling escapes as defined in `spec/core.md §2.2`.
    fn read_string(&mut self) -> Result<String, Value> {
        let mut out = String::new();
        loop {
            let Some(ch) = self.bump() else {
                return Err(reader_error("string eof", Value::Nil));
            };
            match ch {
                '"' => break,
                '\\' => {
                    let esc = self
                        .bump()
                        .ok_or_else(|| reader_error("string escape", Value::Nil))?;
                    match esc {
                        '"' => out.push('"'),
                        '\\' => out.push('\\'),
                        'n' => out.push('\n'),
                        't' => out.push('\t'),
                        'r' => out.push('\r'),
                        'x' => {
                            let hi = self
                                .bump()
                                .ok_or_else(|| reader_error("string hex", Value::Nil))?;
                            let lo = self
                                .bump()
                                .ok_or_else(|| reader_error("string hex", Value::Nil))?;
                            let byte = hex_pair(hi, lo)
                                .ok_or_else(|| reader_error("string hex", Value::Nil))?;
                            out.push(char::from(byte));
                        }
                        other => {
                            return Err(reader_error(
                                "string escape",
                                Value::Str(other.to_string()),
                            ));
                        }
                    }
                }
                other => out.push(other),
            }
        }
        Ok(out)
    }

    /// Handle `#` dispatch sequences; only `#u8` exists in v0.1 (`spec/core.md §2.2`).
    fn read_dispatch(&mut self) -> Result<Value, Value> {
        match (self.bump(), self.bump()) {
            (Some('u'), Some('8')) => {
                if self.bump() != Some('(') {
                    return Err(reader_error("#u8", Value::Nil));
                }
                self.read_byte_list()
            }
            _ => Err(reader_error("dispatch", Value::Nil)),
        }
    }

    /// Parse `#u8(` byte vectors, enforcing 0–255 bounds (`spec/core.md §2.2`).
    fn read_byte_list(&mut self) -> Result<Value, Value> {
        let mut bytes = Vec::new();
        loop {
            self.skip_ws()?;
            match self.peek() {
                Some(')') => {
                    self.bump();
                    return Ok(Value::Bytes(bytes));
                }
                Some(_) => {
                    let Value::Int(n) = self.read_number()? else {
                        unreachable!();
                    };
                    if n.sign() == Sign::Minus {
                        return Err(reader_error("byte", Value::Int(n)));
                    }
                    if let Some(v) = n.to_u8() {
                        bytes.push(v);
                    } else {
                        return Err(reader_error("byte", Value::Int(n)));
                    }
                }
                None => return Err(reader_error("bytes", Value::Nil)),
            }
        }
    }
}

/// Characters that terminate tokens per `spec/core.md §2.2`.
fn is_delimiter(ch: char) -> bool {
    matches!(
        ch,
        ' ' | '\t' | '\n' | '(' | ')' | '"' | ';' | ',' | '`' | '\''
    )
}

/// Validate a symbol component using the identifier grammar (`spec/core.md §2.2`).
fn valid_symbol_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !is_symbol_initial(first) {
        return false;
    }
    chars.all(is_symbol_subsequent)
}

/// Determine whether `ch` is legal as an initial symbol character (`spec/core.md §2.2`).
fn is_symbol_initial(ch: char) -> bool {
    is_xid_start(ch)
        || matches!(
            ch,
            '!' | '$'
                | '%'
                | '&'
                | '*'
                | '+'
                | '-'
                | '.'
                | '/'
                | ':'
                | '<'
                | '='
                | '>'
                | '?'
                | '@'
                | '^'
                | '_'
                | '~'
        )
}

/// Determine whether `ch` may appear after the first symbol character (`spec/core.md §2.2`).
fn is_symbol_subsequent(ch: char) -> bool {
    is_xid_continue(ch) || is_symbol_initial(ch) || ch.is_ascii_digit()
}

/// Parse two hexadecimal digits into a byte; used for string escapes (`spec/core.md §2.2`).
fn hex_pair(hi: char, lo: char) -> Option<u8> {
    fn digit(c: char) -> Option<u8> {
        match c {
            '0'..='9' => Some((c as u8) - b'0'),
            'a'..='f' => Some((c as u8) - b'a' + 10),
            'A'..='F' => Some((c as u8) - b'A' + 10),
            _ => None,
        }
    }
    let hi = digit(hi)?;
    let lo = digit(lo)?;
    Some((hi << 4) | lo)
}

pub fn read_all(source: &str) -> Result<Vec<Value>, Value> {
    Reader::new(source).read_all()
}

#[cfg(test)]
mod tests;

/// Render a byte slice as lowercase hex for debugging (`spec/core.md §11`).
fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}

// --------------------- Canonical Encoding --------------------

// Tags (`spec/core.md §6.1`)
const T_NIL: u8 = 0x00;
const T_INT: u8 = 0x01;
const T_STR: u8 = 0x02;
const T_SYM: u8 = 0x03;
const T_PAIR: u8 = 0x04;
const T_BYTES: u8 = 0x05;
const T_CLOS: u8 = 0x06; // encoded as pair of hashes per spec
const T_ERR: u8 = 0x07;

impl Value {
    /// Serialize the value into canonical TLV bytes (`spec/core.md §6`).
    pub fn encode(&self) -> Vec<u8> {
        match self {
            Value::Nil => vec![T_NIL, 0x00],
            Value::Int(n) => {
                let be = be_twos_complement_from_bigint(n);
                let mut out = vec![T_INT];
                out.extend(uleb128_encode(be.len() as u128));
                out.extend(be);
                out
            }
            Value::Str(s) => {
                let b = s.as_bytes();
                let mut out = vec![T_STR];
                out.extend(uleb128_encode(b.len() as u128));
                out.extend_from_slice(b);
                out
            }
            Value::Sym(sy) => {
                let pk = Value::Str(sy.package.clone());
                let nm = Value::Str(sy.name.clone());
                let id = Value::Bytes(sy.id.to_vec());
                let mut payload = Vec::new();
                payload.extend(pk.encode());
                payload.extend(nm.encode());
                payload.extend(id.encode());
                let mut out = vec![T_SYM];
                out.extend(uleb128_encode(payload.len() as u128));
                out.extend(payload);
                out
            }
            Value::Bytes(b) => {
                let mut out = vec![T_BYTES];
                out.extend(uleb128_encode(b.len() as u128));
                out.extend(b);
                out
            }
            Value::Pair(a, d) => {
                let ea = a.encode();
                let ed = d.encode();
                let mut payload = Vec::with_capacity(ea.len() + ed.len());
                payload.extend(ea);
                payload.extend(ed);
                let mut out = vec![T_PAIR];
                out.extend(uleb128_encode(payload.len() as u128));
                out.extend(payload);
                out
            }
            Value::Closure(c) => {
                // Encode as pair of hashes per `spec/core.md §6.7`.
                let pair = Value::Pair(
                    Rc::new(Value::Bytes(c.code_hash.to_vec())),
                    Rc::new(Value::Bytes(c.env_shape_hash.to_vec())),
                );
                let mut payload = pair.encode();
                let mut out = vec![T_CLOS];
                out.extend(uleb128_encode(payload.len() as u128));
                out.append(&mut payload);
                out
            }
            Value::Error(e) => {
                let code = Value::Sym(e.code.clone()).encode();
                let msg = Value::Str(e.message.clone()).encode();
                let pay = e.payload.encode();
                let mut payload = Vec::new();
                payload.extend(code);
                payload.extend(msg);
                payload.extend(pay);
                let mut out = vec![T_ERR];
                out.extend(uleb128_encode(payload.len() as u128));
                out.extend(payload);
                out
            }
        }
    }

    /// Parse a canonical TLV payload back into a value (`spec/core.md §6`).
    pub fn decode(mut bytes: &[u8]) -> Result<(Value, usize)> {
        if bytes.is_empty() {
            return Err(anyhow!("decode: EOF"));
        }
        let tag = bytes[0];
        bytes = &bytes[1..];
        let (len, used) = if tag == T_NIL {
            (0u128, 0usize)
        } else {
            uleb128_decode(bytes)?
        };
        let mut consumed = 1 + used;
        let mut payload = &bytes[used..];
        if payload.len() < len as usize {
            return Err(anyhow!("decode: bad length"));
        }
        let body = &payload[..len as usize];
        consumed += len as usize;
        match tag {
            T_NIL => Ok((Value::Nil, 1)),
            T_INT => Ok((Value::Int(be_twos_complement_to_bigint(body)), consumed)),
            T_STR => Ok((Value::Str(std::str::from_utf8(body)?.to_string()), consumed)),
            T_BYTES => Ok((Value::Bytes(body.to_vec()), consumed)),
            T_PAIR => {
                let (a, ua) = Value::decode(body)?;
                let (d, ud) = Value::decode(&body[ua..])?;
                if ua + ud != body.len() {
                    return Err(anyhow!("pair decode: trailing"));
                }
                Ok((Value::Pair(Rc::new(a), Rc::new(d)), consumed))
            }
            T_SYM => {
                let (pk, upk) = Value::decode(body)?;
                let (nm, unm) = Value::decode(&body[upk..])?;
                let (idv, uid) = Value::decode(&body[upk + unm..])?;
                if upk + unm + uid != body.len() {
                    return Err(anyhow!("sym decode: trailing"));
                }
                let (package, name, id) = match (pk, nm, idv) {
                    (Value::Str(p), Value::Str(n), Value::Bytes(mut b)) => {
                        if b.len() != 32 {
                            return Err(anyhow!("sym id len"));
                        }
                        let mut id = [0u8; 32];
                        id.copy_from_slice(&b);
                        (p, n, id)
                    }
                    _ => return Err(anyhow!("sym: bad fields")),
                };
                // verify id
                let mut h = Hasher::new();
                h.update(package.as_bytes());
                h.update(&[0]);
                h.update(name.as_bytes());
                if h.finalize().as_bytes() != id {
                    return Err(anyhow!("sym id mismatch"));
                }
                Ok((Value::Sym(Rc::new(Symbol { package, name, id })), consumed))
            }
            T_CLOS => {
                // For hashing only; we decode to an opaque closure placeholder
                let (pair, _u) = Value::decode(body)?;
                let (code_h, env_h) = match pair {
                    Value::Pair(a, d) => (a, d),
                    _ => return Err(anyhow!("closure payload not pair")),
                };
                let (code_hash, env_hash) = match (&*code_h, &*env_h) {
                    (Value::Bytes(c), Value::Bytes(e)) if c.len() == 32 && e.len() == 32 => {
                        let mut ch = [0u8; 32];
                        ch.copy_from_slice(c);
                        let mut eh = [0u8; 32];
                        eh.copy_from_slice(e);
                        (ch, eh)
                    }
                    _ => return Err(anyhow!("closure hashes invalid")),
                };
                Ok((
                    Value::Closure(Rc::new(Closure::opaque(code_hash, env_hash))),
                    consumed,
                ))
            }
            T_ERR => {
                let (code, u1) = Value::decode(body)?;
                let (msg, u2) = Value::decode(&body[u1..])?;
                let (pay, u3) = Value::decode(&body[u1 + u2..])?;
                if u1 + u2 + u3 != body.len() {
                    return Err(anyhow!("error decode trailing"));
                }
                let code = match code {
                    Value::Sym(s) => s,
                    _ => return Err(anyhow!("error code not sym")),
                };
                let message = match msg {
                    Value::Str(s) => s,
                    _ => return Err(anyhow!("error msg not str")),
                };
                Ok((
                    Value::Error(Box::new(ErrorVal {
                        code,
                        message,
                        payload: pay,
                    })),
                    consumed,
                ))
            }
            _ => Err(anyhow!("unknown tag")),
        }
    }

    /// Compute the BLAKE3-256 digest of the canonical encoding (`spec/core.md §7`).
    pub fn hash32(&self) -> [u8; 32] {
        let enc = self.encode();
        let mut h = Hasher::new();
        h.update(&enc);
        let mut out = [0u8; 32];
        out.copy_from_slice(h.finalize().as_bytes());
        out
    }
}

// ------------------------- Bytecode --------------------------

/// Instruction set of the stack VM described in `spec/core.md §8.4`.
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Op {
    Nop = 0x00,
    Halt = 0x01,
    Const = 0x10,
    LRef = 0x11,
    GRef = 0x13,
    Clos = 0x14,
    Pop = 0x15,
    Call = 0x20,
    TCall = 0x21,
    Ret = 0x22,
    IfJ = 0x23,
    Jump = 0x24,
    Cons = 0x30,
    Car = 0x31,
    Cdr = 0x32,
    NullP = 0x40,
    PairP = 0x41,
    IntP = 0x42,
    StrP = 0x43,
    SymP = 0x44,
    BytesP = 0x45,
    ClosP = 0x46,
    ErrP = 0x47,
    Eq = 0x48,
    Equal = 0x49,
    Add = 0x50,
    Sub = 0x51,
    Mul = 0x52,
    Div = 0x53,
    Mod = 0x54,
    Abs = 0x55,
    Neg = 0x56,
    Cmp = 0x57,
    Shl = 0x58,
    Shr = 0x59,
    BAnd = 0x5A,
    BOr = 0x5B,
    BXor = 0x5C,
    BNot = 0x5D,
    StrLen = 0x60,
    StrRef = 0x61,
    StrCat = 0x62,
    BtLen = 0x63,
    BtRef = 0x64,
    BtSlice = 0x65,
    Utf8Enc = 0x66,
    Utf8Dec = 0x67,
    Sym = 0x70,
    SymName = 0x71,
    SymPkg = 0x72,
    Raise = 0x80,
    IsErr = 0x81,
    ErrNew = 0x82,
    ErrCode = 0x83,
    ErrMsg = 0x84,
    ErrPayload = 0x85,
    Hash = 0x90,
    Encode = 0x91,
    Decode = 0x92,
}

// Function and module containers (`spec/core.md §8.1–§8.3`)
/// Compiled function object per `spec/core.md §8.2`.
#[derive(Clone)]
pub struct Function {
    pub arity: u16,
    pub nlocals: u16,
    pub code: Vec<u8>,
}

/// Module container that groups constants, functions, and exports (`spec/core.md §8.1`).
#[derive(Clone)]
pub struct Module {
    pub consts: Vec<Value>,
    pub functions: Vec<Function>,
    pub exports: BTreeMap<[u8; 32], (Rc<Symbol>, u16)>,
    pub hash: [u8; 32],
}

impl Module {
    pub fn new(
        consts: Vec<Value>,
        functions: Vec<Function>,
        exports: Vec<(Rc<Symbol>, u16)>,
    ) -> Self {
        let mut export_map = BTreeMap::new();
        for (sym, idx) in exports {
            export_map.insert(sym.id, (sym, idx));
        }
        // Hash module manifest (simple, deterministic)
        let mut h = Hasher::new();
        for c in &consts {
            h.update(&c.encode());
        }
        for f in &functions {
            h.update(&f.arity.to_be_bytes());
            h.update(&f.nlocals.to_be_bytes());
            h.update(&(f.code.len() as u32).to_be_bytes());
            h.update(&f.code);
        }
        for (id, (_, idx)) in &export_map {
            h.update(id);
            h.update(&idx.to_be_bytes());
        }
        let mut hash = [0u8; 32];
        hash.copy_from_slice(h.finalize().as_bytes());
        Self {
            consts,
            functions,
            exports: export_map,
            hash,
        }
    }

    pub fn export(&self, sym: &Symbol) -> Option<(Rc<Symbol>, u16)> {
        self.exports.get(&sym.id).cloned()
    }
}

// --------------------- Closures & Frames ---------------------

/// Closure capturing a function index and its environment (`spec/core.md §4/§8.3`).
#[derive(Clone)]
pub struct Closure {
    pub module: Rc<Module>,
    pub func_idx: u16,
    pub env: Vec<Rc<Value>>, // captured cells
    pub code_hash: [u8; 32],
    pub env_shape_hash: [u8; 32],
}

impl Closure {
    /// Instantiate a closure over a module function and lexical environment (`spec/core.md §4`).
    pub fn new(module: Rc<Module>, func_idx: u16, env: Vec<Rc<Value>>) -> Self {
        let func = &module.functions[func_idx as usize];
        // code hash: blake3 over function code bytes
        let mut hc = Hasher::new();
        hc.update(&func.code);
        let mut ch = [0u8; 32];
        ch.copy_from_slice(hc.finalize().as_bytes());
        // env shape hash: hashes of captured values' hashes (structure only)
        let mut he = Hasher::new();
        for v in &env {
            he.update(&v.hash32());
        }
        let mut eh = [0u8; 32];
        eh.copy_from_slice(he.finalize().as_bytes());
        Self {
            module,
            func_idx,
            env,
            code_hash: ch,
            env_shape_hash: eh,
        }
    }
    /// Synthesize an opaque closure from hashes for decoding (`spec/core.md §6.7`).
    pub fn opaque(code_hash: [u8; 32], env_hash: [u8; 32]) -> Self {
        Self {
            module: Rc::new(Module {
                consts: vec![],
                functions: vec![],
                exports: BTreeMap::new(),
                hash: [0u8; 32],
            }),
            func_idx: 0,
            env: vec![],
            code_hash,
            env_shape_hash: env_hash,
        }
    }
}

/// Activation frame tracking interpreter state (`spec/core.md §8.3`).
#[derive(Clone)]
struct Frame {
    module: Rc<Module>,
    func_idx: u16,
    ip: usize,
    locals: Vec<Rc<Value>>,   // size = function.nlocals
    env: Vec<Vec<Rc<Value>>>, // lexical env chain: [captured, caller's envs...]
}

// --------------------------- VM ------------------------------

/// Reference bytecode VM implementing the evaluator in `spec/core.md §5/§8`.
pub struct VM {
    stack: Vec<Rc<Value>>,
    frames: Vec<Frame>,
}

impl VM {
    /// Create an empty VM with no modules loaded.
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            frames: Vec::new(),
        }
    }

    /// Push a raw value onto the operand stack (`spec/core.md §8.3`).
    fn push(&mut self, v: Value) {
        self.stack.push(Rc::new(v));
    }
    /// Pop the stack, producing a reader-style error value on underflow (`spec/core.md §8.3`).
    fn pop(&mut self) -> Rc<Value> {
        self.stack.pop().unwrap_or_else(|| {
            Rc::new(Value::Error(Box::new(ErrorVal {
                code: Rc::new(Symbol::new("error", "stack")),
                message: "underflow".into(),
                payload: Value::Nil,
            })))
        })
    }

    /// Borrow the current activation frame; VM invariants guarantee it exists.
    fn current_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("no frame")
    }

    /// Resolve `export` in `module` and invoke it as the program entry (`spec/core.md §12`).
    pub fn call_main(&mut self, module: Rc<Module>, export: &Symbol) -> Value {
        let Some((_, idx)) = module.export(export) else {
            return Value::Error(Box::new(ErrorVal {
                code: Rc::new(Symbol::new("error", "link")),
                message: "missing export".into(),
                payload: Value::Sym(Rc::new(export.clone())),
            }));
        };
        let clos = Closure::new(module.clone(), idx, vec![]);
        self.apply_closure(Rc::new(clos), &[])
    }

    /// Read a big-endian `u16` operand and advance the instruction pointer.
    fn load_u16(code: &[u8], ip: &mut usize) -> u16 {
        let v = u16::from_be_bytes([code[*ip], code[*ip + 1]]);
        *ip += 2;
        v
    }
    /// Read a big-endian `i16` operand and advance the instruction pointer.
    fn load_i16(code: &[u8], ip: &mut usize) -> i16 {
        let v = i16::from_be_bytes([code[*ip], code[*ip + 1]]);
        *ip += 2;
        v
    }

    /// Structural equality predicate backing `equal?` (`spec/core.md §5.6`).
    fn value_eq(a: &Value, b: &Value) -> bool {
        match (a, b) {
            (Value::Int(x), Value::Int(y)) => x == y,
            (Value::Str(x), Value::Str(y)) => x == y,
            (Value::Bytes(x), Value::Bytes(y)) => x == y,
            (Value::Sym(x), Value::Sym(y)) => x.id == y.id,
            (Value::Nil, Value::Nil) => true,
            (Value::Pair(ax, ad), Value::Pair(bx, bd)) => {
                Self::value_eq(ax.as_ref(), bx.as_ref()) && Self::value_eq(ad.as_ref(), bd.as_ref())
            }
            (Value::Error(ex), Value::Error(ey)) => {
                ex.code.id == ey.code.id
                    && ex.message == ey.message
                    && Self::value_eq(&ex.payload, &ey.payload)
            }
            (Value::Closure(cx), Value::Closure(cy)) => {
                cx.code_hash == cy.code_hash && cx.env_shape_hash == cy.env_shape_hash
            }
            _ => false,
        }
    }

    /// Extract a big integer or raise a typed error (`spec/core.md §5.2`).
    fn as_int(v: &Value) -> Result<BigInt> {
        if let Value::Int(n) = v {
            Ok(n.clone())
        } else {
            Err(anyhow!("type:int"))
        }
    }

    /// Execute a primitive opcode by mutating the stack (`spec/core.md §5`).
    fn apply_primitive(&mut self, op: Op) {
        use Value::*;
        let err = |code: &str, msg: &str, payload: Value| -> Value {
            Value::Error(Box::new(ErrorVal {
                code: Rc::new(Symbol::new("error", code)),
                message: msg.into(),
                payload,
            }))
        };
        match op {
            Op::Cons => {
                let d = self.pop();
                let a = self.pop();
                self.push(Pair(a, d));
            }
            Op::Car => {
                let p = self.pop();
                match &*p {
                    Pair(a, _) => self.stack.push(a.clone()),
                    _ => self.push(err("type", "car expects pair", (*p).clone())),
                }
            }
            Op::Cdr => {
                let p = self.pop();
                match &*p {
                    Pair(_, d) => self.stack.push(d.clone()),
                    _ => self.push(err("type", "cdr expects pair", (*p).clone())),
                }
            }
            Op::NullP => {
                let x = self.pop();
                self.push(Int(if matches!(&*x, Nil) {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }));
            }
            Op::PairP => {
                let x = self.pop();
                self.push(Int(if matches!(&*x, Pair(_, _)) {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }));
            }
            Op::IntP => {
                let x = self.pop();
                self.push(Int(if matches!(&*x, Int(_)) {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }));
            }
            Op::StrP => {
                let x = self.pop();
                self.push(Int(if matches!(&*x, Str(_)) {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }));
            }
            Op::SymP => {
                let x = self.pop();
                self.push(Int(if matches!(&*x, Sym(_)) {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }));
            }
            Op::BytesP => {
                let x = self.pop();
                self.push(Int(if matches!(&*x, Bytes(_)) {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }));
            }
            Op::ClosP => {
                let x = self.pop();
                self.push(Int(if matches!(&*x, Closure(_)) {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }));
            }
            Op::ErrP => {
                let x = self.pop();
                self.push(Int(if matches!(&*x, Error(_)) {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }));
            }
            Op::Eq => {
                let b = self.pop();
                let a = self.pop();
                let eq = match (&*a, &*b) {
                    (Sym(x), Sym(y)) => x.id == y.id,
                    (Int(x), Int(y)) => x == y,
                    (Str(x), Str(y)) => x == y,
                    (Bytes(x), Bytes(y)) => x == y,
                    (Pair(_, _), Pair(_, _)) => a.hash32() == b.hash32(),
                    (Closure(x), Closure(y)) => {
                        x.code_hash == y.code_hash && x.env_shape_hash == y.env_shape_hash
                    }
                    _ => false,
                };
                self.push(Int(if eq { BigInt::one() } else { BigInt::zero() }));
            }
            Op::Equal => {
                let b = self.pop();
                let a = self.pop();
                self.push(Int(if Self::value_eq(a.as_ref(), b.as_ref()) {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }));
            }
            Op::Add
            | Op::Sub
            | Op::Mul
            | Op::Div
            | Op::Mod
            | Op::Abs
            | Op::Neg
            | Op::Cmp
            | Op::Shl
            | Op::Shr
            | Op::BAnd
            | Op::BOr
            | Op::BXor
            | Op::BNot => {
                // Numeric core
                match op {
                    Op::Abs => {
                        let a = self.pop();
                        match &*a {
                            Int(n) => self.push(Int(n.abs())),
                            _ => self.push(err("type", "abs expects int", (*a).clone())),
                        }
                    }
                    Op::Neg => {
                        let a = self.pop();
                        match &*a {
                            Int(n) => self.push(Int(-n.clone())),
                            _ => self.push(err("type", "neg expects int", (*a).clone())),
                        }
                    }
                    Op::BNot => {
                        let a = self.pop();
                        match &*a {
                            Int(n) => {
                                // bit-not: two's complement infinite
                                // ~x = -x - 1
                                self.push(Int((-n.clone()) - BigInt::one()));
                            }
                            _ => self.push(err("type", "bnot expects int", (*a).clone())),
                        }
                    }
                    _ => {
                        let b = self.pop();
                        let a = self.pop();
                        let ai = Self::as_int(&a);
                        let bi = Self::as_int(&b);
                        if let (Ok(a), Ok(b)) = (ai, bi) {
                            let v = match op {
                                Op::Add => a + b,
                                Op::Sub => a - b,
                                Op::Mul => a * b,
                                Op::Div => {
                                    if b.is_zero() {
                                        self.push(err(
                                            "domain",
                                            "div by zero",
                                            Value::Pair(
                                                Rc::new((*a).clone()),
                                                Rc::new((*b).clone()),
                                            ),
                                        ));
                                        return;
                                    } // Euclidean floor toward -inf
                                    let q0 = a.clone() / b.clone();
                                    let r = a.clone() % b.clone();
                                    let needs_fix = ((a.sign() == Sign::Minus)
                                        ^ (b.sign() == Sign::Minus))
                                        && !r.is_zero();
                                    if needs_fix {
                                        q0 - BigInt::one()
                                    } else {
                                        q0
                                    }
                                }
                                Op::Mod => {
                                    if b.is_zero() {
                                        self.push(err(
                                            "domain",
                                            "mod by zero",
                                            Value::Pair(
                                                Rc::new((*a).clone()),
                                                Rc::new((*b).clone()),
                                            ),
                                        ));
                                        return;
                                    }
                                    let mut r = a.clone() % b.clone();
                                    let needs_fix = ((a.sign() == Sign::Minus)
                                        ^ (b.sign() == Sign::Minus))
                                        && !r.is_zero();
                                    if needs_fix {
                                        r += b.clone();
                                    }
                                    r
                                }
                                Op::Cmp => {
                                    if a < b {
                                        BigInt::from(-1)
                                    } else if a > b {
                                        BigInt::one()
                                    } else {
                                        BigInt::zero()
                                    }
                                }
                                Op::Shl => {
                                    // n>=0
                                    if b.sign() == Sign::Minus {
                                        self.push(err(
                                            "domain",
                                            "shl negative shift",
                                            (*b).clone(),
                                        ));
                                        return;
                                    }
                                    let k = b.to_usize().unwrap_or(usize::MAX / 2);
                                    a << k
                                }
                                Op::Shr => {
                                    if b.sign() == Sign::Minus {
                                        self.push(err(
                                            "domain",
                                            "shr negative shift",
                                            (*b).clone(),
                                        ));
                                        return;
                                    }
                                    let k = b.to_usize().unwrap_or(usize::MAX / 2);
                                    // Arithmetic shift right: floor(a / 2^k) toward -inf
                                    if k == 0 {
                                        a
                                    } else {
                                        // Use div with 2^k
                                        let two = BigInt::from(2u32);
                                        let pow = two.pow(k as u32);
                                        let q0 = a.clone() / pow.clone();
                                        let r = a.clone() % pow;
                                        let needs_fix = a.sign() == Sign::Minus && !r.is_zero();
                                        if needs_fix {
                                            q0 - BigInt::one()
                                        } else {
                                            q0
                                        }
                                    }
                                }
                                Op::BAnd => {
                                    // emulate bit ops via two's complement width = max(bitlen(a), bitlen(b))
                                    bitop_and(&a, &b)
                                }
                                Op::BOr => bitop_or(&a, &b),
                                Op::BXor => bitop_xor(&a, &b),
                                _ => unreachable!(),
                            };
                            self.push(Int(v));
                        } else {
                            self.push(err("type", "numeric op expects ints", Value::Pair(a, b)));
                        }
                    }
                }
            }
            Op::StrLen => {
                let s = self.pop();
                match &*s {
                    Value::Str(st) => self.push(Value::Int(BigInt::from(st.chars().count()))),
                    _ => self.push(err("type", "strlen expects string", (*s).clone())),
                }
            }
            Op::StrRef => {
                let i = self.pop();
                let s = self.pop();
                match (&*s, Self::as_int(&i)) {
                    (Value::Str(st), Ok(idx)) => {
                        if idx.sign() == Sign::Minus {
                            self.push(err("bounds", "str-ref", (*i).clone()));
                        } else if let Some(pos) = idx.to_usize() {
                            if let Some(ch) = st.chars().nth(pos) {
                                self.push(Value::Int(BigInt::from(u32::from(ch))));
                            } else {
                                self.push(err("bounds", "str-ref", (*i).clone()));
                            }
                        } else {
                            self.push(err("bounds", "str-ref", (*i).clone()));
                        }
                    }
                    _ => self.push(err(
                        "type",
                        "str-ref expects (string int)",
                        Value::Pair(s, i),
                    )),
                }
            }
            Op::StrCat => {
                let b = self.pop();
                let a = self.pop();
                match (&*a, &*b) {
                    (Value::Str(x), Value::Str(y)) => self.push(Value::Str(format!("{}{}", x, y))),
                    _ => self.push(err("type", "strcat expects strings", Value::Pair(a, b))),
                }
            }
            Op::BtLen => {
                let s = self.pop();
                match &*s {
                    Value::Bytes(bt) => self.push(Value::Int(BigInt::from(bt.len()))),
                    _ => self.push(err("type", "bytes-len expects bytes", (*s).clone())),
                }
            }
            Op::BtRef => {
                let i = self.pop();
                let b = self.pop();
                match (&*b, Self::as_int(&i)) {
                    (Value::Bytes(bytes), Ok(idx)) => {
                        if idx.sign() == Sign::Minus {
                            self.push(err("bounds", "bytes-ref", (*i).clone()));
                        } else if let Some(pos) = idx.to_usize() {
                            if let Some(byte) = bytes.get(pos) {
                                self.push(Value::Int(BigInt::from(*byte)));
                            } else {
                                self.push(err("bounds", "bytes-ref", (*i).clone()));
                            }
                        } else {
                            self.push(err("bounds", "bytes-ref", (*i).clone()));
                        }
                    }
                    _ => self.push(err(
                        "type",
                        "bytes-ref expects (bytes int)",
                        Value::Pair(b, i),
                    )),
                }
            }
            Op::BtSlice => {
                let j = self.pop();
                let i = self.pop();
                let b = self.pop();
                match (&*b, Self::as_int(&i), Self::as_int(&j)) {
                    (Value::Bytes(bytes), Ok(ii), Ok(jj)) => {
                        if ii.sign() == Sign::Minus || jj.sign() == Sign::Minus {
                            self.push(err("bounds", "slice", (*b).clone()));
                        } else if let (Some(start), Some(end)) = (ii.to_usize(), jj.to_usize()) {
                            if start > end || end > bytes.len() {
                                self.push(err("bounds", "slice", (*b).clone()));
                            } else {
                                self.push(Value::Bytes(bytes[start..end].to_vec()));
                            }
                        } else {
                            self.push(err("bounds", "slice", (*b).clone()));
                        }
                    }
                    _ => self.push(err(
                        "type",
                        "bytes-slice expects bytes,int,int",
                        Value::Pair(
                            b,
                            Rc::new(Value::Pair(Rc::new((*i).clone()), Rc::new((*j).clone()))),
                        ),
                    )),
                }
            }
            Op::Utf8Enc => {
                let s = self.pop();
                match &*s {
                    Value::Str(st) => self.push(Value::Bytes(st.as_bytes().to_vec())),
                    _ => self.push(err("type", "utf8-encode expects string", (*s).clone())),
                }
            }
            Op::Utf8Dec => {
                let b = self.pop();
                match &*b {
                    Value::Bytes(bt) => match std::str::from_utf8(bt) {
                        Ok(s) => self.push(Value::Str(s.to_string())),
                        Err(_) => self.push(err("encoding", "invalid utf8", (*b).clone())),
                    },
                    _ => self.push(err("type", "utf8-decode expects bytes", (*b).clone())),
                }
            }
            Op::Sym => {
                let name = self.pop();
                let pkg = self.pop();
                match (&*pkg, &*name) {
                    (Value::Str(p), Value::Str(n)) => {
                        self.push(Value::Sym(Rc::new(Symbol::new(p.clone(), n.clone()))))
                    }
                    _ => self.push(err("type", "sym expects strings", Value::Pair(pkg, name))),
                }
            }
            Op::SymName => {
                let s = self.pop();
                match &*s {
                    Value::Sym(sym) => self.push(Value::Str(sym.name.clone())),
                    _ => self.push(err("type", "sym-name expects symbol", (*s).clone())),
                }
            }
            Op::SymPkg => {
                let s = self.pop();
                match &*s {
                    Value::Sym(sym) => self.push(Value::Str(sym.package.clone())),
                    _ => self.push(err("type", "sym-package expects symbol", (*s).clone())),
                }
            }
            Op::Raise => {
                let x = self.pop();
                match &*x {
                    Value::Error(_) => self.stack.push(x.clone()),
                    _ => self.push(Value::Error(Box::new(ErrorVal {
                        code: Rc::new(Symbol::new("error", "raised")),
                        message: "raised".into(),
                        payload: (*x).clone(),
                    }))),
                }
            }
            Op::IsErr => {
                let x = self.pop();
                self.push(Value::Int(if matches!(&*x, Value::Error(_)) {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }));
            }
            Op::ErrNew => {
                let pay = self.pop();
                let msg = self.pop();
                let code = self.pop();
                match (&*code, &*msg) {
                    (Value::Sym(c), Value::Str(m)) => self.push(Value::Error(Box::new(ErrorVal {
                        code: c.clone(),
                        message: m.clone(),
                        payload: (*pay).clone(),
                    }))),
                    _ => self.push(err(
                        "type",
                        "error expects (sym str any)",
                        Value::Pair(code, Rc::new(Value::Pair(msg, pay))),
                    )),
                }
            }
            Op::ErrCode => {
                let e = self.pop();
                match &*e {
                    Value::Error(ev) => self.push(Value::Sym(ev.code.clone())),
                    _ => self.push(err("type", "error-code expects error", (*e).clone())),
                }
            }
            Op::ErrMsg => {
                let e = self.pop();
                match &*e {
                    Value::Error(ev) => self.push(Value::Str(ev.message.clone())),
                    _ => self.push(err("type", "error-msg expects error", (*e).clone())),
                }
            }
            Op::ErrPayload => {
                let e = self.pop();
                match &*e {
                    Value::Error(ev) => self.push(ev.payload.clone()),
                    _ => self.push(err("type", "error-payload expects error", (*e).clone())),
                }
            }
            Op::Hash => {
                let v = self.pop();
                self.push(Value::Bytes(v.hash32().to_vec()));
            }
            Op::Encode => {
                let v = self.pop();
                self.push(Value::Bytes(v.encode()));
            }
            Op::Decode => {
                let b = self.pop();
                match &*b {
                    Value::Bytes(bytes) => match Value::decode(bytes) {
                        Ok((v, _)) => self.push(v),
                        Err(e) => self.push(err("decode", &e.to_string(), (*b).clone())),
                    },
                    _ => self.push(err("type", "decode expects bytes", (*b).clone())),
                }
            }
            _ => {
                // Control, env and others are handled elsewhere; unknown → error
                self.push(Value::Error(Box::new(ErrorVal {
                    code: Rc::new(Symbol::new("error", "bytecode")),
                    message: format!("unimplemented op {op:?}"),
                    payload: Value::Nil,
                })));
            }
        }
    }

    fn apply_closure(&mut self, clos: Rc<Closure>, args: &[Rc<Value>]) -> Value {
        let func = &clos.module.functions[clos.func_idx as usize];
        if args.len() != func.arity as usize {
            return Value::Error(Box::new(ErrorVal {
                code: Rc::new(Symbol::new("error", "arity")),
                message: "arity".into(),
                payload: Value::Int(BigInt::from(args.len() as i32)),
            }));
        }
        // New frame
        let mut locals = Vec::with_capacity(func.nlocals as usize);
        for a in args {
            locals.push(a.clone());
        }
        while locals.len() < func.nlocals as usize {
            locals.push(Rc::new(Value::Nil));
        }
        let env_chain = vec![clos.env.clone()];
        self.frames.push(Frame {
            module: clos.module.clone(),
            func_idx: clos.func_idx,
            ip: 0,
            locals,
            env: env_chain,
        });
        // Run
        let result = self.run_current();
        result
    }

    fn run_current(&mut self) -> Value {
        loop {
            if self.frames.is_empty() {
                return Value::Nil;
            }
            let (module, func_idx, ip) = {
                let fr = self.frames.last().unwrap();
                (fr.module.clone(), fr.func_idx, fr.ip)
            };
            let func = &module.functions[func_idx as usize];
            if ip >= func.code.len() {
                return Value::Error(Box::new(ErrorVal {
                    code: Rc::new(Symbol::new("error", "ip")),
                    message: "ip past end".into(),
                    payload: Value::Nil,
                }));
            }
            let mut ip = ip;
            let op = unsafe { std::mem::transmute::<u8, Op>(func.code[ip]) };
            ip += 1;
            // Save back ip by default; some ops will override
            self.frames.last_mut().unwrap().ip = ip;
            match op {
                Op::Nop => {}
                Op::Halt => {
                    let v = self.pop();
                    self.frames.clear();
                    return (*v).clone();
                }
                Op::Const => {
                    let k = Self::load_u16(&func.code, &mut ip);
                    self.frames.last_mut().unwrap().ip = ip;
                    let v = module.consts[k as usize].clone();
                    self.push(v);
                }
                Op::LRef => {
                    let depth = Self::load_u16(&func.code, &mut ip) as usize;
                    let index = Self::load_u16(&func.code, &mut ip) as usize;
                    self.frames.last_mut().unwrap().ip = ip;
                    if depth == 0 {
                        // local
                        let v = self
                            .frames
                            .last()
                            .unwrap()
                            .locals
                            .get(index)
                            .cloned()
                            .unwrap_or_else(|| Rc::new(Value::Nil));
                        self.stack.push(v);
                    } else {
                        // captured
                        let env = &self.frames.last().unwrap().env;
                        if depth - 1 >= env.len() {
                            self.push(Value::Error(Box::new(ErrorVal {
                                code: Rc::new(Symbol::new("error", "env")),
                                message: "bad depth".into(),
                                payload: Value::Nil,
                            })));
                        } else {
                            let cell = env[depth - 1]
                                .get(index)
                                .cloned()
                                .unwrap_or_else(|| Rc::new(Value::Nil));
                            self.stack.push(cell);
                        }
                    }
                }
                Op::GRef => {
                    // Resolve global by export index order — for simplicity we assume a const Sym was pushed then GRef resolves it; in fuller linker we'd map indices.
                    // Here: GRef k => push export function as Closure with empty env.
                    let k = Self::load_u16(&func.code, &mut ip);
                    self.frames.last_mut().unwrap().ip = ip;
                    let func_idx = k; // simple model
                    let clos = Closure::new(module.clone(), func_idx, vec![]);
                    self.stack.push(Rc::new(Value::Closure(Rc::new(clos))));
                }
                Op::Clos => {
                    let fidx = Self::load_u16(&func.code, &mut ip);
                    let nfree = Self::load_u16(&func.code, &mut ip) as usize;
                    self.frames.last_mut().unwrap().ip = ip;
                    let mut captured = Vec::with_capacity(nfree);
                    for _ in 0..nfree {
                        let v = self.pop();
                        captured.push(v);
                    }
                    captured.reverse();
                    let clos = Closure::new(module.clone(), fidx, captured);
                    self.stack.push(Rc::new(Value::Closure(Rc::new(clos))));
                }
                Op::Pop => {
                    let _ = self.pop();
                }
                Op::Call | Op::TCall => {
                    let nargs = Self::load_u16(&func.code, &mut ip) as usize;
                    self.frames.last_mut().unwrap().ip = ip;
                    // collect args
                    let mut args = Vec::with_capacity(nargs);
                    for _ in 0..nargs {
                        args.push(self.pop());
                    }
                    args.reverse();
                    let f = self.pop();
                    match &*f {
                        Value::Closure(c) => {
                            if op == Op::TCall {
                                // Replace current frame (tail-call)
                                let callee = &c.module.functions[c.func_idx as usize];
                                if nargs != callee.arity as usize {
                                    self.push(Value::Error(Box::new(ErrorVal {
                                        code: Rc::new(Symbol::new("error", "arity")),
                                        message: "arity".into(),
                                        payload: Value::Nil,
                                    })));
                                } else {
                                    let mut locals = Vec::with_capacity(callee.nlocals as usize);
                                    for a in &args {
                                        locals.push(a.clone());
                                    }
                                    while locals.len() < callee.nlocals as usize {
                                        locals.push(Rc::new(Value::Nil));
                                    }
                                    let env_chain = vec![c.env.clone()];
                                    let top = self.frames.last_mut().unwrap();
                                    top.module = c.module.clone();
                                    top.func_idx = c.func_idx;
                                    top.ip = 0;
                                    top.locals = locals;
                                    top.env = env_chain;
                                }
                            } else {
                                let res = self.apply_closure(c.clone(), &args);
                                self.push(res);
                            }
                        }
                        other => {
                            // Primitive application not via CALL; use opcodes for primitives. If attempted, return error value.
                            self.push(Value::Error(Box::new(ErrorVal {
                                code: Rc::new(Symbol::new("error", "apply")),
                                message: "apply non-closure".into(),
                                payload: (*other).clone(),
                            })));
                        }
                    }
                }
                Op::Ret => {
                    let v = self.pop();
                    let _ = self.frames.pop();
                    if self.frames.is_empty() {
                        return (*v).clone();
                    } else {
                        self.stack.push(v);
                    }
                }
                Op::IfJ => {
                    let off = Self::load_i16(&func.code, &mut ip);
                    // test top of stack
                    let test = self.pop();
                    let falsey = matches!(&*test, Value::Nil)
                        || matches!(&*test, Value::Int(n) if n.is_zero());
                    if falsey {
                        let new_ip = (ip as isize) + (off as isize);
                        if new_ip < 0 || new_ip as usize > func.code.len() {
                            return Value::Error(Box::new(ErrorVal {
                                code: Rc::new(Symbol::new("error", "jump")),
                                message: "ifj target".into(),
                                payload: Value::Nil,
                            }));
                        }
                        self.frames.last_mut().unwrap().ip = new_ip as usize;
                    } else {
                        self.frames.last_mut().unwrap().ip = ip;
                    }
                }
                Op::Jump => {
                    let off = Self::load_i16(&func.code, &mut ip);
                    let new_ip = (ip as isize) + (off as isize);
                    if new_ip < 0 || new_ip as usize > func.code.len() {
                        return Value::Error(Box::new(ErrorVal {
                            code: Rc::new(Symbol::new("error", "jump")),
                            message: "target".into(),
                            payload: Value::Nil,
                        }));
                    }
                    self.frames.last_mut().unwrap().ip = new_ip as usize;
                }
                // Primitive opcodes
                op if matches!(
                    op,
                    Op::Cons
                        | Op::Car
                        | Op::Cdr
                        | Op::NullP
                        | Op::PairP
                        | Op::IntP
                        | Op::StrP
                        | Op::SymP
                        | Op::BytesP
                        | Op::ClosP
                        | Op::ErrP
                        | Op::Eq
                        | Op::Equal
                        | Op::Add
                        | Op::Sub
                        | Op::Mul
                        | Op::Div
                        | Op::Mod
                        | Op::Abs
                        | Op::Neg
                        | Op::Cmp
                        | Op::Shl
                        | Op::Shr
                        | Op::BAnd
                        | Op::BOr
                        | Op::BXor
                        | Op::BNot
                        | Op::StrLen
                        | Op::StrRef
                        | Op::StrCat
                        | Op::BtLen
                        | Op::BtRef
                        | Op::BtSlice
                        | Op::Utf8Enc
                        | Op::Utf8Dec
                        | Op::Sym
                        | Op::SymName
                        | Op::SymPkg
                        | Op::Raise
                        | Op::IsErr
                        | Op::ErrNew
                        | Op::ErrCode
                        | Op::ErrMsg
                        | Op::ErrPayload
                        | Op::Hash
                        | Op::Encode
                        | Op::Decode
                ) =>
                {
                    self.apply_primitive(op);
                }
                _ => {
                    // Push error value and continue
                    self.push(Value::Error(Box::new(ErrorVal {
                        code: Rc::new(Symbol::new("error", "bytecode")),
                        message: format!("unknown or unimpl op {op:?}"),
                        payload: Value::Nil,
                    })));
                }
            }
        }
    }
}

// ------- Bitwise helpers with minimal-width two's-complement -------
fn bit_width(n: &BigInt) -> usize {
    be_twos_complement_from_bigint(n).len() * 8
}
fn choose_width(a: &BigInt, b: &BigInt) -> usize {
    bit_width(a).max(bit_width(b))
}
/// Shared helper to implement `(bit-and ...)` semantics (`spec/core.md §5.4`).
fn bitop_and(a: &BigInt, b: &BigInt) -> BigInt {
    let w = choose_width(a, b);
    let (ab, bb) = (
        be_twos_complement_from_bigint(a),
        be_twos_complement_from_bigint(b),
    );
    let aw = to_fixed_width(&ab, w);
    let bw = to_fixed_width(&bb, w);
    let mut out = vec![0u8; aw.len()];
    for i in 0..aw.len() {
        out[i] = aw[i] & bw[i];
    }
    be_twos_complement_to_bigint(&out)
}
/// Shared helper to implement `(bit-or ...)` semantics (`spec/core.md §5.4`).
fn bitop_or(a: &BigInt, b: &BigInt) -> BigInt {
    let w = choose_width(a, b);
    let aw = to_fixed_width(&be_twos_complement_from_bigint(a), w);
    let bw = to_fixed_width(&be_twos_complement_from_bigint(b), w);
    let mut out = vec![0u8; aw.len()];
    for i in 0..aw.len() {
        out[i] = aw[i] | bw[i];
    }
    be_twos_complement_to_bigint(&out)
}
/// Shared helper to implement `(bit-xor ...)` semantics (`spec/core.md §5.4`).
fn bitop_xor(a: &BigInt, b: &BigInt) -> BigInt {
    let w = choose_width(a, b);
    let aw = to_fixed_width(&be_twos_complement_from_bigint(a), w);
    let bw = to_fixed_width(&be_twos_complement_from_bigint(b), w);
    let mut out = vec![0u8; aw.len()];
    for i in 0..aw.len() {
        out[i] = aw[i] ^ bw[i];
    }
    be_twos_complement_to_bigint(&out)
}
fn to_fixed_width(be: &[u8], w_bits: usize) -> Vec<u8> {
    // Ensure exactly w_bits two's complement width
    let bytes = (w_bits + 7) / 8;
    let neg = (be[0] & 0x80) != 0;
    let mut out = vec![if neg { 0xFF } else { 0x00 }; bytes];
    let src = be;
    // copy least significant bytes (right aligned)
    let n = src.len().min(bytes);
    out[(bytes - n)..].copy_from_slice(&src[(src.len() - n)..]);
    out
}

// --------------------------- Demo ----------------------------

fn build_demo_module() -> Rc<Module> {
    // Build a module with one function main/0 that computes ((1+2)*3) and halts.
    // consts: [1,2,3]
    let consts = vec![
        Value::Int(1.into()),
        Value::Int(2.into()),
        Value::Int(3.into()),
    ];
    // code: CONST 0; CONST 1; ADD; CONST 2; MUL; HALT
    let mut code = Vec::new();
    code.push(Op::Const as u8);
    code.extend_from_slice(&0u16.to_be_bytes());
    code.push(Op::Const as u8);
    code.extend_from_slice(&1u16.to_be_bytes());
    code.push(Op::Add as u8);
    code.push(Op::Const as u8);
    code.extend_from_slice(&2u16.to_be_bytes());
    code.push(Op::Mul as u8);
    code.push(Op::Halt as u8);
    let func = Function {
        arity: 0,
        nlocals: 0,
        code,
    };
    let exports = vec![(Rc::new(Symbol::new("user", "main")), 0)];
    Rc::new(Module::new(consts, vec![func], exports))
}

fn main() {
    let module = build_demo_module();
    let mut vm = VM::new();
    let result = vm.call_main(module.clone(), &Symbol::new("user", "main"));
    println!("Result: {result:?}");
}
