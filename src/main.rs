// OFLISP Reference VM (Rust) — v0.1
// ------------------------------------------------------------
// Rreference interpreter + bytecode VM for Operating Function LISP
//

use anyhow::{anyhow, ensure, Result};
use blake3::Hasher;
use num_bigint::{BigInt, Sign};
use num_traits::{One, ToPrimitive, Zero};
use std::collections::{BTreeMap, HashMap};
use std::fmt::{self, Debug, Display};
use std::rc::Rc;
use unicode_ident::{is_xid_continue, is_xid_start};

// ------------------------- Utilities -------------------------

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

// ---------------------- Snapshot Engine ----------------------

type Handle = u32;

const SNAPSHOT_MAGIC: &[u8; 8] = b"OFSNAP02";
const SNAPSHOT_VERSION: u32 = 1;

#[derive(Clone, Debug)]
struct SymbolSnapshot {
    package: String,
    name: String,
    id: [u8; 32],
}

impl SymbolSnapshot {
    fn from_symbol(sym: &Symbol) -> Self {
        Self {
            package: sym.package.clone(),
            name: sym.name.clone(),
            id: sym.id,
        }
    }

    fn into_symbol(self) -> Result<Rc<Symbol>> {
        let rebuilt = Symbol::new(self.package.clone(), self.name.clone());
        ensure!(
            rebuilt.id == self.id,
            "symbol digest mismatch while decoding snapshot"
        );
        Ok(Rc::new(rebuilt))
    }
}

#[derive(Clone, Debug)]
enum HeapNode {
    Nil,
    Int(Vec<u8>),
    Str(String),
    Sym(SymbolSnapshot),
    Bytes(Vec<u8>),
    Pair {
        car: Handle,
        cdr: Handle,
    },
    Closure {
        module_hash: [u8; 32],
        func_idx: u16,
        env: Vec<Handle>,
        code_hash: [u8; 32],
        env_shape_hash: [u8; 32],
    },
    Error {
        code: SymbolSnapshot,
        message: String,
        payload: Handle,
    },
}

#[derive(Clone, Debug)]
pub struct SnapshotFrame {
    module_hash: [u8; 32],
    func_idx: u16,
    ip: u32,
    locals: Vec<Handle>,
    env: Vec<Vec<Handle>>,
}

#[derive(Clone, Debug)]
pub struct Snapshot {
    heap: Vec<HeapNode>,
    stack: Vec<Handle>,
    frames: Vec<SnapshotFrame>,
}

pub trait ModuleResolver {
    fn resolve(&self, hash: &[u8; 32]) -> Option<Rc<Module>>;
}

impl Snapshot {
    pub fn encode(&self) -> Result<Vec<u8>> {
        ensure!(
            self.heap.len() < u32::MAX as usize,
            "snapshot heap exceeds supported size"
        );
        let mut out = Vec::new();
        out.extend_from_slice(SNAPSHOT_MAGIC);
        out.extend_from_slice(&SNAPSHOT_VERSION.to_be_bytes());
        out.extend_from_slice(&(self.heap.len() as u32).to_be_bytes());
        for node in &self.heap {
            encode_heap_node(&mut out, node)?;
        }
        out.extend_from_slice(&(self.stack.len() as u32).to_be_bytes());
        for handle in &self.stack {
            out.extend_from_slice(&handle.to_be_bytes());
        }
        out.extend_from_slice(&(self.frames.len() as u32).to_be_bytes());
        for frame in &self.frames {
            out.extend_from_slice(&frame.module_hash);
            out.extend_from_slice(&frame.func_idx.to_be_bytes());
            out.extend_from_slice(&frame.ip.to_be_bytes());
            out.extend_from_slice(&(frame.locals.len() as u32).to_be_bytes());
            for handle in &frame.locals {
                out.extend_from_slice(&handle.to_be_bytes());
            }
            out.extend_from_slice(&(frame.env.len() as u32).to_be_bytes());
            for scope in &frame.env {
                out.extend_from_slice(&(scope.len() as u32).to_be_bytes());
                for handle in scope {
                    out.extend_from_slice(&handle.to_be_bytes());
                }
            }
        }
        let mut hasher = Hasher::new();
        hasher.update(&out);
        out.extend_from_slice(hasher.finalize().as_bytes());
        Ok(out)
    }

    pub fn decode(bytes: &[u8]) -> Result<Self> {
        ensure!(
            bytes.len() >= SNAPSHOT_MAGIC.len() + 4 + 32,
            "snapshot payload too small"
        );
        let (content, digest_bytes) = bytes.split_at(bytes.len() - 32);
        let mut hasher = Hasher::new();
        hasher.update(content);
        ensure!(
            hasher.finalize().as_bytes() == digest_bytes,
            "snapshot digest mismatch"
        );
        let mut cursor = 0usize;
        ensure!(
            &content[cursor..cursor + SNAPSHOT_MAGIC.len()] == SNAPSHOT_MAGIC,
            "snapshot magic mismatch"
        );
        cursor += SNAPSHOT_MAGIC.len();
        let version = read_u32(content, &mut cursor)?;
        ensure!(version == SNAPSHOT_VERSION, "unsupported snapshot version");
        let heap_len = read_u32(content, &mut cursor)? as usize;
        let mut heap = Vec::with_capacity(heap_len);
        for _ in 0..heap_len {
            heap.push(decode_heap_node(content, &mut cursor)?);
        }
        let stack_len = read_u32(content, &mut cursor)? as usize;
        let mut stack = Vec::with_capacity(stack_len);
        for _ in 0..stack_len {
            stack.push(read_handle(content, &mut cursor)?);
        }
        let frame_len = read_u32(content, &mut cursor)? as usize;
        let mut frames = Vec::with_capacity(frame_len);
        for _ in 0..frame_len {
            let mut module_hash = [0u8; 32];
            module_hash.copy_from_slice(read_bytes(content, &mut cursor, 32)?);
            let func_idx = read_u16(content, &mut cursor)?;
            let ip = read_u32(content, &mut cursor)?;
            let locals_len = read_u32(content, &mut cursor)? as usize;
            let mut locals = Vec::with_capacity(locals_len);
            for _ in 0..locals_len {
                locals.push(read_handle(content, &mut cursor)?);
            }
            let env_len = read_u32(content, &mut cursor)? as usize;
            let mut env = Vec::with_capacity(env_len);
            for _ in 0..env_len {
                let scope_len = read_u32(content, &mut cursor)? as usize;
                let mut scope = Vec::with_capacity(scope_len);
                for _ in 0..scope_len {
                    scope.push(read_handle(content, &mut cursor)?);
                }
                env.push(scope);
            }
            frames.push(SnapshotFrame {
                module_hash,
                func_idx,
                ip,
                locals,
                env,
            });
        }
        ensure!(cursor == content.len(), "trailing data in snapshot");
        Ok(Self {
            heap,
            stack,
            frames,
        })
    }

    fn materialize(
        &self,
        handle: Handle,
        cache: &mut [Option<Rc<Value>>],
        modules: &dyn ModuleResolver,
    ) -> Result<Rc<Value>> {
        let idx = usize::try_from(handle).map_err(|_| anyhow!("bad handle index"))?;
        if let Some(existing) = &cache[idx] {
            return Ok(existing.clone());
        }
        let value = match &self.heap[idx] {
            HeapNode::Nil => Rc::new(Value::Nil),
            HeapNode::Int(bytes) => Rc::new(Value::Int(be_twos_complement_to_bigint(bytes))),
            HeapNode::Str(s) => Rc::new(Value::Str(s.clone())),
            HeapNode::Sym(sym) => Rc::new(Value::Sym(sym.clone().into_symbol()?)),
            HeapNode::Bytes(b) => Rc::new(Value::Bytes(b.clone())),
            HeapNode::Pair { car, cdr } => {
                let car_v = self.materialize(*car, cache, modules)?;
                let cdr_v = self.materialize(*cdr, cache, modules)?;
                Rc::new(Value::Pair(car_v, cdr_v))
            }
            HeapNode::Closure {
                module_hash,
                func_idx,
                env,
                code_hash,
                env_shape_hash,
            } => {
                let module = modules
                    .resolve(module_hash)
                    .ok_or_else(|| anyhow!("unknown module in closure"))?;
                ensure!(module.hash == *module_hash, "closure module hash mismatch");
                let captured = env
                    .iter()
                    .map(|h| self.materialize(*h, cache, modules))
                    .collect::<Result<Vec<_>>>()?;
                let clos = Closure::new(module.clone(), *func_idx, captured);
                ensure!(clos.code_hash == *code_hash, "closure code hash mismatch");
                ensure!(
                    clos.env_shape_hash == *env_shape_hash,
                    "closure environment hash mismatch"
                );
                Rc::new(Value::Closure(Rc::new(clos)))
            }
            HeapNode::Error {
                code,
                message,
                payload,
            } => {
                let payload_v = self.materialize(*payload, cache, modules)?;
                Rc::new(Value::Error(Box::new(ErrorVal {
                    code: code.clone().into_symbol()?,
                    message: message.clone(),
                    payload: (*payload_v).clone(),
                })))
            }
        };
        cache[idx] = Some(value.clone());
        Ok(value)
    }
}

fn encode_heap_node(out: &mut Vec<u8>, node: &HeapNode) -> Result<()> {
    match node {
        HeapNode::Nil => out.push(0x00),
        HeapNode::Int(bytes) => {
            out.push(0x01);
            write_bytes(out, bytes);
        }
        HeapNode::Str(s) => {
            out.push(0x02);
            write_bytes(out, s.as_bytes());
        }
        HeapNode::Sym(sym) => {
            out.push(0x03);
            write_bytes(out, sym.package.as_bytes());
            write_bytes(out, sym.name.as_bytes());
            out.extend_from_slice(&sym.id);
        }
        HeapNode::Bytes(b) => {
            out.push(0x04);
            write_bytes(out, b);
        }
        HeapNode::Pair { car, cdr } => {
            out.push(0x05);
            out.extend_from_slice(&car.to_be_bytes());
            out.extend_from_slice(&cdr.to_be_bytes());
        }
        HeapNode::Closure {
            module_hash,
            func_idx,
            env,
            code_hash,
            env_shape_hash,
        } => {
            ensure!(env.len() < u32::MAX as usize, "closure env too large");
            out.push(0x06);
            out.extend_from_slice(module_hash);
            out.extend_from_slice(&func_idx.to_be_bytes());
            out.extend_from_slice(&(env.len() as u32).to_be_bytes());
            for handle in env {
                out.extend_from_slice(&handle.to_be_bytes());
            }
            out.extend_from_slice(code_hash);
            out.extend_from_slice(env_shape_hash);
        }
        HeapNode::Error {
            code,
            message,
            payload,
        } => {
            out.push(0x07);
            write_bytes(out, code.package.as_bytes());
            write_bytes(out, code.name.as_bytes());
            out.extend_from_slice(&code.id);
            write_bytes(out, message.as_bytes());
            out.extend_from_slice(&payload.to_be_bytes());
        }
    }
    Ok(())
}

fn decode_heap_node(bytes: &[u8], cursor: &mut usize) -> Result<HeapNode> {
    let tag = read_u8(bytes, cursor)?;
    Ok(match tag {
        0x00 => HeapNode::Nil,
        0x01 => HeapNode::Int(read_blob(bytes, cursor)?),
        0x02 => HeapNode::Str(String::from_utf8(read_blob(bytes, cursor)?)?),
        0x03 => {
            let package = String::from_utf8(read_blob(bytes, cursor)?)?;
            let name = String::from_utf8(read_blob(bytes, cursor)?)?;
            let mut id = [0u8; 32];
            id.copy_from_slice(read_bytes(bytes, cursor, 32)?);
            HeapNode::Sym(SymbolSnapshot { package, name, id })
        }
        0x04 => HeapNode::Bytes(read_blob(bytes, cursor)?),
        0x05 => {
            let car = read_handle(bytes, cursor)?;
            let cdr = read_handle(bytes, cursor)?;
            HeapNode::Pair { car, cdr }
        }
        0x06 => {
            let mut module_hash = [0u8; 32];
            module_hash.copy_from_slice(read_bytes(bytes, cursor, 32)?);
            let func_idx = read_u16(bytes, cursor)?;
            let env_len = read_u32(bytes, cursor)? as usize;
            let mut env = Vec::with_capacity(env_len);
            for _ in 0..env_len {
                env.push(read_handle(bytes, cursor)?);
            }
            let mut code_hash = [0u8; 32];
            code_hash.copy_from_slice(read_bytes(bytes, cursor, 32)?);
            let mut env_shape_hash = [0u8; 32];
            env_shape_hash.copy_from_slice(read_bytes(bytes, cursor, 32)?);
            HeapNode::Closure {
                module_hash,
                func_idx,
                env,
                code_hash,
                env_shape_hash,
            }
        }
        0x07 => {
            let package = String::from_utf8(read_blob(bytes, cursor)?)?;
            let name = String::from_utf8(read_blob(bytes, cursor)?)?;
            let mut id = [0u8; 32];
            id.copy_from_slice(read_bytes(bytes, cursor, 32)?);
            let message = String::from_utf8(read_blob(bytes, cursor)?)?;
            let payload = read_handle(bytes, cursor)?;
            HeapNode::Error {
                code: SymbolSnapshot { package, name, id },
                message,
                payload,
            }
        }
        _ => return Err(anyhow!("unknown heap tag in snapshot")),
    })
}

fn read_bytes<'a>(bytes: &'a [u8], cursor: &mut usize, len: usize) -> Result<&'a [u8]> {
    if bytes.len() < *cursor + len {
        return Err(anyhow!("snapshot truncated"));
    }
    let slice = &bytes[*cursor..*cursor + len];
    *cursor += len;
    Ok(slice)
}

fn read_blob(bytes: &[u8], cursor: &mut usize) -> Result<Vec<u8>> {
    let len = read_u32(bytes, cursor)? as usize;
    Ok(read_bytes(bytes, cursor, len)?.to_vec())
}

fn read_u8(bytes: &[u8], cursor: &mut usize) -> Result<u8> {
    if bytes.len() <= *cursor {
        return Err(anyhow!("snapshot truncated"));
    }
    let v = bytes[*cursor];
    *cursor += 1;
    Ok(v)
}

fn read_u16(bytes: &[u8], cursor: &mut usize) -> Result<u16> {
    let slice = read_bytes(bytes, cursor, 2)?;
    Ok(u16::from_be_bytes([slice[0], slice[1]]))
}

fn read_u32(bytes: &[u8], cursor: &mut usize) -> Result<u32> {
    let slice = read_bytes(bytes, cursor, 4)?;
    Ok(u32::from_be_bytes([slice[0], slice[1], slice[2], slice[3]]))
}

fn read_handle(bytes: &[u8], cursor: &mut usize) -> Result<Handle> {
    Ok(read_u32(bytes, cursor)?)
}

fn write_bytes(out: &mut Vec<u8>, data: &[u8]) {
    out.extend_from_slice(&(data.len() as u32).to_be_bytes());
    out.extend_from_slice(data);
}

struct SnapshotBuilder {
    handles: HashMap<usize, Handle>,
    heap: Vec<HeapNode>,
    keepalive: Vec<Rc<Value>>,
}

impl SnapshotBuilder {
    fn new() -> Self {
        Self {
            handles: HashMap::new(),
            heap: Vec::new(),
            keepalive: Vec::new(),
        }
    }

    fn intern_rc(&mut self, value: Rc<Value>) -> Result<Handle> {
        let ptr = Rc::as_ptr(&value) as usize;
        if let Some(&handle) = self.handles.get(&ptr) {
            return Ok(handle);
        }
        let index = self.heap.len();
        ensure!(index < u32::MAX as usize, "snapshot heap overflow");
        let handle = index as Handle;
        self.handles.insert(ptr, handle);
        self.keepalive.push(value.clone());
        self.heap.push(HeapNode::Nil);
        let node = match value.as_ref() {
            Value::Nil => HeapNode::Nil,
            Value::Int(n) => HeapNode::Int(be_twos_complement_from_bigint(n)),
            Value::Str(s) => HeapNode::Str(s.clone()),
            Value::Sym(sym) => HeapNode::Sym(SymbolSnapshot::from_symbol(sym)),
            Value::Bytes(b) => HeapNode::Bytes(b.clone()),
            Value::Pair(a, d) => {
                let car = self.intern_rc(a.clone())?;
                let cdr = self.intern_rc(d.clone())?;
                HeapNode::Pair { car, cdr }
            }
            Value::Closure(c) => {
                let env = c
                    .env
                    .iter()
                    .map(|cell| self.intern_rc(cell.clone()))
                    .collect::<Result<Vec<_>>>()?;
                HeapNode::Closure {
                    module_hash: c.module.hash,
                    func_idx: c.func_idx,
                    env,
                    code_hash: c.code_hash,
                    env_shape_hash: c.env_shape_hash,
                }
            }
            Value::Error(err) => {
                let payload = self.intern_value(err.payload.clone())?;
                HeapNode::Error {
                    code: SymbolSnapshot::from_symbol(&err.code),
                    message: err.message.clone(),
                    payload,
                }
            }
        };
        self.heap[index] = node;
        Ok(handle)
    }

    fn intern_value(&mut self, value: Value) -> Result<Handle> {
        self.intern_rc(Rc::new(value))
    }

    fn finish(self, stack: Vec<Handle>, frames: Vec<SnapshotFrame>) -> Result<Snapshot> {
        Ok(Snapshot {
            heap: self.heap,
            stack,
            frames,
        })
    }
}

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

#[derive(Clone)]
pub struct Symbol {
    pub package: String,
    pub name: String,
    pub id: [u8; 32],
}

impl Symbol {
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
    pub fn truthy(&self) -> bool {
        match self {
            Value::Nil => false,
            Value::Int(n) => !n.is_zero(),
            _ => true,
        }
    }
    pub fn is_error(&self) -> bool {
        matches!(self, Value::Error(_))
    }

    /// Produce the canonical external representation required by §11.
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

fn int_to_hex(nibble: u8) -> char {
    match nibble {
        0..=9 => (b'0' + nibble) as char,
        10..=15 => (b'A' + (nibble - 10)) as char,
        _ => unreachable!(),
    }
}

fn canonical_symbol(sym: &Symbol) -> String {
    let name = canonical_symbol_component(&sym.name);
    if sym.package == "user" {
        name
    } else {
        let pkg = canonical_symbol_component(&sym.package);
        format!("{pkg}/{name}")
    }
}

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

fn requires_symbol_quoting(component: &str) -> bool {
    component.chars().any(|ch| {
        ch.is_whitespace()
            || matches!(
                ch,
                '(' | ')' | '"' | '\'' | '`' | ',' | '@' | '|' | ';' | '#' | '[' | ']' | '{' | '}'
            )
    })
}

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

fn reader_error(message: &str, payload: Value) -> Value {
    Value::Error(Box::new(ErrorVal {
        code: Rc::new(Symbol::new("error", "reader")),
        message: message.to_string(),
        payload,
    }))
}

fn list_from(items: Vec<Value>) -> Value {
    let mut acc = Value::Nil;
    for item in items.into_iter().rev() {
        acc = Value::Pair(Rc::new(item), Rc::new(acc));
    }
    acc
}

fn list2(a: Value, b: Value) -> Value {
    list_from(vec![a, b])
}

fn symbol(name: &str) -> Value {
    Value::Sym(Rc::new(Symbol::new("user", name)))
}

struct Reader<'a> {
    chars: std::str::Chars<'a>,
    offset: usize,
}

impl<'a> Reader<'a> {
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

    fn after_dot_delimited(&self) -> bool {
        let mut iter = self.chars.clone();
        iter.next();
        match iter.next() {
            None => true,
            Some(ch) => is_delimiter(ch),
        }
    }

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

fn is_delimiter(ch: char) -> bool {
    matches!(
        ch,
        ' ' | '\t' | '\n' | '(' | ')' | '"' | ';' | ',' | '`' | '\''
    )
}

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

fn is_symbol_subsequent(ch: char) -> bool {
    is_xid_continue(ch) || is_symbol_initial(ch) || ch.is_ascii_digit()
}

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

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}

// --------------------- Canonical Encoding --------------------

// Tags (§6.1)
const T_NIL: u8 = 0x00;
const T_INT: u8 = 0x01;
const T_STR: u8 = 0x02;
const T_SYM: u8 = 0x03;
const T_PAIR: u8 = 0x04;
const T_BYTES: u8 = 0x05;
const T_CLOS: u8 = 0x06; // encoded as pair of hashes per spec
const T_ERR: u8 = 0x07;

impl Value {
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
                // Encode as pair of hashes per spec (§6.7)
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

// Function and module containers (§8.1–8.3)
#[derive(Clone)]
pub struct Function {
    pub arity: u16,
    pub nlocals: u16,
    pub code: Vec<u8>,
}

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

#[derive(Clone)]
pub struct Closure {
    pub module: Rc<Module>,
    pub func_idx: u16,
    pub env: Vec<Rc<Value>>, // captured cells
    pub code_hash: [u8; 32],
    pub env_shape_hash: [u8; 32],
}

impl Closure {
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

#[derive(Clone)]
pub(crate) struct Frame {
    module: Rc<Module>,
    func_idx: u16,
    ip: usize,
    locals: Vec<Rc<Value>>,   // size = function.nlocals
    env: Vec<Vec<Rc<Value>>>, // lexical env chain: [captured, caller's envs...]
}

// --------------------------- VM ------------------------------

pub struct VM {
    stack: Vec<Rc<Value>>,
    frames: Vec<Frame>,
}

impl VM {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            frames: Vec::new(),
        }
    }

    fn push(&mut self, v: Value) {
        self.stack.push(Rc::new(v));
    }
    fn pop(&mut self) -> Rc<Value> {
        self.stack.pop().unwrap_or_else(|| {
            Rc::new(Value::Error(Box::new(ErrorVal {
                code: Rc::new(Symbol::new("error", "stack")),
                message: "underflow".into(),
                payload: Value::Nil,
            })))
        })
    }

    fn current_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("no frame")
    }

    /// Serialize the live runtime state into a persistent snapshot (§6, roadmap v0.2).
    pub fn snapshot(&self) -> Result<Snapshot> {
        let mut builder = SnapshotBuilder::new();
        let stack = self
            .stack
            .iter()
            .map(|v| builder.intern_rc(v.clone()))
            .collect::<Result<Vec<_>>>()?;
        let mut frames = Vec::with_capacity(self.frames.len());
        for frame in &self.frames {
            let ip = u32::try_from(frame.ip)
                .map_err(|_| anyhow!("frame instruction pointer exceeds snapshot width"))?;
            let locals = frame
                .locals
                .iter()
                .map(|v| builder.intern_rc(v.clone()))
                .collect::<Result<Vec<_>>>()?;
            let mut env = Vec::with_capacity(frame.env.len());
            for scope in &frame.env {
                env.push(
                    scope
                        .iter()
                        .map(|v| builder.intern_rc(v.clone()))
                        .collect::<Result<Vec<_>>>()?,
                );
            }
            frames.push(SnapshotFrame {
                module_hash: frame.module.hash,
                func_idx: frame.func_idx,
                ip,
                locals,
                env,
            });
        }
        builder.finish(stack, frames)
    }

    /// Restore a VM from a previously captured snapshot (§6, roadmap v0.2).
    pub fn restore(snapshot: &Snapshot, modules: &dyn ModuleResolver) -> Result<Self> {
        let mut cache: Vec<Option<Rc<Value>>> = vec![None; snapshot.heap.len()];
        let stack = snapshot
            .stack
            .iter()
            .map(|h| snapshot.materialize(*h, &mut cache, modules))
            .collect::<Result<Vec<_>>>()?;
        let mut frames_out = Vec::with_capacity(snapshot.frames.len());
        for frame in &snapshot.frames {
            let module = modules
                .resolve(&frame.module_hash)
                .ok_or_else(|| anyhow!("unknown module in snapshot"))?;
            ensure!(
                module.hash == frame.module_hash,
                "module hash mismatch during restore"
            );
            let locals = frame
                .locals
                .iter()
                .map(|h| snapshot.materialize(*h, &mut cache, modules))
                .collect::<Result<Vec<_>>>()?;
            let mut env = Vec::with_capacity(frame.env.len());
            for scope in &frame.env {
                env.push(
                    scope
                        .iter()
                        .map(|h| snapshot.materialize(*h, &mut cache, modules))
                        .collect::<Result<Vec<_>>>()?,
                );
            }
            frames_out.push(Frame {
                module,
                func_idx: frame.func_idx,
                ip: frame.ip as usize,
                locals,
                env,
            });
        }
        Ok(Self {
            stack,
            frames: frames_out,
        })
    }

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

    fn load_u16(code: &[u8], ip: &mut usize) -> u16 {
        let v = u16::from_be_bytes([code[*ip], code[*ip + 1]]);
        *ip += 2;
        v
    }
    fn load_i16(code: &[u8], ip: &mut usize) -> i16 {
        let v = i16::from_be_bytes([code[*ip], code[*ip + 1]]);
        *ip += 2;
        v
    }

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

    fn as_int(v: &Value) -> Result<BigInt> {
        if let Value::Int(n) = v {
            Ok(n.clone())
        } else {
            Err(anyhow!("type:int"))
        }
    }

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

#[cfg(test)]
impl VM {
    pub(crate) fn push_rc(&mut self, value: Rc<Value>) {
        self.stack.push(value);
    }

    pub(crate) fn push_frame(&mut self, frame: Frame) {
        self.frames.push(frame);
    }

    pub(crate) fn stack_ref(&self) -> &[Rc<Value>] {
        &self.stack
    }

    pub(crate) fn frames_ref(&self) -> &[Frame] {
        &self.frames
    }
}

impl Frame {
    #[cfg(test)]
    pub(crate) fn new_for_test(
        module: Rc<Module>,
        func_idx: u16,
        ip: usize,
        locals: Vec<Rc<Value>>,
        env: Vec<Vec<Rc<Value>>>,
    ) -> Self {
        Self {
            module,
            func_idx,
            ip,
            locals,
            env,
        }
    }

    #[cfg(test)]
    pub(crate) fn locals_ref(&self) -> &[Rc<Value>] {
        &self.locals
    }

    #[cfg(test)]
    pub(crate) fn env_ref(&self) -> &[Vec<Rc<Value>>] {
        &self.env
    }
}

// ------- Bitwise helpers with minimal-width two's-complement -------
fn bit_width(n: &BigInt) -> usize {
    be_twos_complement_from_bigint(n).len() * 8
}
fn choose_width(a: &BigInt, b: &BigInt) -> usize {
    bit_width(a).max(bit_width(b))
}
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
