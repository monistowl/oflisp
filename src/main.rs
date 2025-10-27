// OFLISP Reference VM (Rust) — v0.1
// ------------------------------------------------------------
// Rreference interpreter + bytecode VM for Operating Function LISP
//

use anyhow::{anyhow, Result};
use blake3::Hasher;
use num_bigint::{BigInt, Sign};
use num_traits::{One, Zero, ToPrimitive};
use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display};
use std::rc::Rc;

// ------------------------- Utilities -------------------------

fn uleb128_encode(mut n: u128) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let mut byte = (n & 0x7F) as u8;
        n >>= 7;
        if n != 0 { byte |= 0x80; }
        out.push(byte);
        if n == 0 { break; }
    }
    out
}

fn uleb128_decode(mut bytes: &[u8]) -> Result<(u128, usize)> {
    let mut result: u128 = 0;
    let mut shift = 0u32;
    let mut used = 0usize;
    loop {
        if bytes.is_empty() { return Err(anyhow!("ULEB128: unexpected EOF")); }
        let b = bytes[0];
        bytes = &bytes[1..];
        used += 1;
        result |= ((b & 0x7F) as u128) << shift;
        if (b & 0x80) == 0 { break; }
        shift += 7;
        if shift > 126 { return Err(anyhow!("ULEB128: too large")); }
    }
    Ok((result, used))
}

fn be_twos_complement_from_bigint(n: &BigInt) -> Vec<u8> {
    // Minimal-width big-endian two's complement, with zero as 0x00.
    if n.is_zero() { return vec![0u8]; }
    let (sign, mut mag) = n.to_bytes_be();
    match sign {
        Sign::Plus => {
            // Ensure the top bit is 0 (positive), minimal length
            if mag[0] & 0x80 != 0 { mag.insert(0, 0x00); }
            // Strip redundant leading 0x00
            while mag.len() > 1 && mag[0] == 0x00 && (mag[1] & 0x80) == 0 { mag.remove(0); }
            mag
        }
        Sign::Minus => {
            // Represent magnitude as two's complement negative.
            // Algorithm: form minimal positive width, then two's complement.
            if mag[0] & 0x80 == 0 { mag.insert(0, 0x00); }
            // Invert
            for b in mag.iter_mut() { *b = !*b; }
            // Add 1
            let mut carry = 1u16;
            for i in (0..mag.len()).rev() {
                let v = (mag[i] as u16) + carry;
                mag[i] = (v & 0xFF) as u8;
                carry = v >> 8;
            }
            // Ensure leading 0xFF and minimal
            if mag[0] != 0xFF { mag.insert(0, 0xFF); }
            while mag.len() > 1 && mag[0] == 0xFF && (mag[1] & 0x80) != 0 { mag.remove(0); }
            mag
        }
        Sign::NoSign => vec![0],
    }
}

fn be_twos_complement_to_bigint(bytes: &[u8]) -> BigInt {
    if bytes.is_empty() { return BigInt::zero(); }
    let neg = (bytes[0] & 0x80) != 0;
    if !neg {
        BigInt::from_bytes_be(Sign::Plus, bytes)
    } else {
        // Two's complement negative: invert and add 1, then negate
        let mut inv = bytes.to_vec();
        for b in inv.iter_mut() { *b = !*b; }
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
pub struct Symbol { pub package: String, pub name: String, pub id: [u8; 32] }

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

impl Debug for Symbol { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}/{}", self.package, self.name) } }

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
pub struct ErrorVal { pub code: Rc<Symbol>, pub message: String, pub payload: Value }

impl Debug for ErrorVal { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "#<error {}:{}>", self.code.name, self.message) } }

impl Value {
    pub fn truthy(&self) -> bool {
        match self {
            Value::Nil => false,
            Value::Int(n) => !n.is_zero(),
            _ => true,
        }
    }
    pub fn is_error(&self) -> bool { matches!(self, Value::Error(_)) }
}

impl Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Nil => write!(f, "()"),
            Value::Int(n) => write!(f, "{}", n),
            Value::Str(s) => write!(f, "\"{}\"", s),
            Value::Sym(sy) => write!(f, "{sy:?}"),
            Value::Bytes(b) => write!(f, "#u8({})", b.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ")),
            Value::Pair(a, d) => write!(f, "({a:?} . {d:?})"),
            Value::Closure(c) => write!(f, "#<closure code={} env={}>", hex(&c.code_hash), hex(&c.env_shape_hash)),
            Value::Error(e) => write!(f, "{e:?}"),
        }
    }
}

fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{:02x}", x)).collect() }

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
                let pair = Value::Pair(Rc::new(Value::Bytes(c.code_hash.to_vec())), Rc::new(Value::Bytes(c.env_shape_hash.to_vec())));
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
        if bytes.is_empty() { return Err(anyhow!("decode: EOF")); }
        let tag = bytes[0];
        bytes = &bytes[1..];
        let (len, used) = if tag == T_NIL { (0u128, 0usize) } else { uleb128_decode(bytes)? };
        let mut consumed = 1 + used;
        let mut payload = &bytes[used..];
        if payload.len() < len as usize { return Err(anyhow!("decode: bad length")); }
        let body = &payload[..len as usize];
        consumed += len as usize;
        match tag {
            T_NIL => Ok((Value::Nil, 1)),
            T_INT => { Ok((Value::Int(be_twos_complement_to_bigint(body)), consumed)) }
            T_STR => { Ok((Value::Str(std::str::from_utf8(body)?.to_string()), consumed)) }
            T_BYTES => { Ok((Value::Bytes(body.to_vec()), consumed)) }
            T_PAIR => {
                let (a, ua) = Value::decode(body)?;
                let (d, ud) = Value::decode(&body[ua..])?;
                if ua + ud != body.len() { return Err(anyhow!("pair decode: trailing")); }
                Ok((Value::Pair(Rc::new(a), Rc::new(d)), consumed))
            }
            T_SYM => {
                let (pk, upk) = Value::decode(body)?; let (nm, unm) = Value::decode(&body[upk..])?; let (idv, uid) = Value::decode(&body[upk+unm..])?;
                if upk + unm + uid != body.len() { return Err(anyhow!("sym decode: trailing")); }
                let (package, name, id) = match (pk, nm, idv) {
                    (Value::Str(p), Value::Str(n), Value::Bytes(mut b)) => {
                        if b.len() != 32 { return Err(anyhow!("sym id len")); }
                        let mut id = [0u8;32]; id.copy_from_slice(&b);
                        (p, n, id)
                    }
                    _ => return Err(anyhow!("sym: bad fields"))
                };
                // verify id
                let mut h = Hasher::new(); h.update(package.as_bytes()); h.update(&[0]); h.update(name.as_bytes());
                if h.finalize().as_bytes() != id { return Err(anyhow!("sym id mismatch")); }
                Ok((Value::Sym(Rc::new(Symbol{package, name, id})), consumed))
            }
            T_CLOS => {
                // For hashing only; we decode to an opaque closure placeholder
                let (pair, _u) = Value::decode(body)?;
                let (code_h, env_h) = match pair {
                    Value::Pair(a, d) => (a, d),
                    _ => return Err(anyhow!("closure payload not pair"))
                };
                let (code_hash, env_hash) = match (&*code_h, &*env_h) {
                    (Value::Bytes(c), Value::Bytes(e)) if c.len()==32 && e.len()==32 => {
                        let mut ch=[0u8;32]; ch.copy_from_slice(c);
                        let mut eh=[0u8;32]; eh.copy_from_slice(e);
                        (ch, eh)
                    }
                    _ => return Err(anyhow!("closure hashes invalid"))
                };
                Ok((Value::Closure(Rc::new(Closure::opaque(code_hash, env_hash))), consumed))
            }
            T_ERR => {
                let (code, u1) = Value::decode(body)?; let (msg, u2) = Value::decode(&body[u1..])?; let (pay, u3) = Value::decode(&body[u1+u2..])?;
                if u1+u2+u3 != body.len() { return Err(anyhow!("error decode trailing")); }
                let code = match code { Value::Sym(s)=>s, _=> return Err(anyhow!("error code not sym")) };
                let message = match msg { Value::Str(s)=>s, _=> return Err(anyhow!("error msg not str")) };
                Ok((Value::Error(Box::new(ErrorVal{ code, message, payload: pay})), consumed))
            }
            _ => Err(anyhow!("unknown tag")),
        }
    }

    pub fn hash32(&self) -> [u8;32] {
        let enc = self.encode();
        let mut h = Hasher::new();
        h.update(&enc);
        let mut out=[0u8;32]; out.copy_from_slice(h.finalize().as_bytes()); out
    }
}

// ------------------------- Bytecode --------------------------

#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Op {
    Nop=0x00, Halt=0x01,
    Const=0x10, LRef=0x11, GRef=0x13, Clos=0x14, Pop=0x15,
    Call=0x20, TCall=0x21, Ret=0x22, IfJ=0x23, Jump=0x24,
    Cons=0x30, Car=0x31, Cdr=0x32,
    NullP=0x40, PairP=0x41, IntP=0x42, StrP=0x43, SymP=0x44, BytesP=0x45, ClosP=0x46, ErrP=0x47,
    Eq=0x48, Equal=0x49,
    Add=0x50, Sub=0x51, Mul=0x52, Div=0x53, Mod=0x54, Abs=0x55, Neg=0x56, Cmp=0x57,
    Shl=0x58, Shr=0x59, BAnd=0x5A, BOr=0x5B, BXor=0x5C, BNot=0x5D,
    StrLen=0x60, StrRef=0x61, StrCat=0x62, BtLen=0x63, BtRef=0x64, BtSlice=0x65, Utf8Enc=0x66, Utf8Dec=0x67,
    Sym=0x70, SymName=0x71, SymPkg=0x72,
    Raise=0x80, IsErr=0x81, ErrNew=0x82, ErrCode=0x83, ErrMsg=0x84, ErrPayload=0x85,
    Hash=0x90, Encode=0x91, Decode=0x92,
}

// Function and module containers (§8.1–8.3)
#[derive(Clone)]
pub struct Function { pub arity: u16, pub nlocals: u16, pub code: Vec<u8> }

#[derive(Clone)]
pub struct Module {
    pub consts: Vec<Value>,
    pub functions: Vec<Function>,
    pub exports: BTreeMap<Rc<Symbol>, u16>,
    pub hash: [u8;32],
}

impl Module {
    pub fn new(consts: Vec<Value>, functions: Vec<Function>, exports: BTreeMap<Rc<Symbol>, u16>) -> Self {
        // Hash module manifest (simple, deterministic)
        let mut h = Hasher::new();
        for c in &consts { h.update(&c.encode()); }
        for f in &functions { h.update(&f.arity.to_be_bytes()); h.update(&f.nlocals.to_be_bytes()); h.update(&(f.code.len() as u32).to_be_bytes()); h.update(&f.code); }
        // export set
        for (k,v) in &exports { h.update(&k.id); h.update(&v.to_be_bytes()); }
        let mut hash=[0u8;32]; hash.copy_from_slice(h.finalize().as_bytes());
        Self{ consts, functions, exports, hash }
    }
}

// --------------------- Closures & Frames ---------------------

#[derive(Clone)]
pub struct Closure {
    pub module: Rc<Module>,
    pub func_idx: u16,
    pub env: Vec<Rc<Value>>, // captured cells
    pub code_hash: [u8;32],
    pub env_shape_hash: [u8;32],
}

impl Closure {
    pub fn new(module: Rc<Module>, func_idx: u16, env: Vec<Rc<Value>>) -> Self {
        let func = &module.functions[func_idx as usize];
        // code hash: blake3 over function code bytes
        let mut hc=Hasher::new(); hc.update(&func.code); let mut ch=[0u8;32]; ch.copy_from_slice(hc.finalize().as_bytes());
        // env shape hash: hashes of captured values' hashes (structure only)
        let mut he=Hasher::new();
        for v in &env { he.update(&v.hash32()); }
        let mut eh=[0u8;32]; eh.copy_from_slice(he.finalize().as_bytes());
        Self { module, func_idx, env, code_hash: ch, env_shape_hash: eh }
    }
    pub fn opaque(code_hash:[u8;32], env_hash:[u8;32]) -> Self {
        Self{ module: Rc::new(Module{ consts:vec![], functions:vec![], exports: BTreeMap::new(), hash:[0u8;32]}), func_idx:0, env:vec![], code_hash, env_shape_hash: env_hash }
    }
}

#[derive(Clone)]
struct Frame {
    module: Rc<Module>,
    func_idx: u16,
    ip: usize,
    locals: Vec<Rc<Value>>, // size = function.nlocals
    env: Vec<Vec<Rc<Value>>>, // lexical env chain: [captured, caller's envs...]
}

// --------------------------- VM ------------------------------

pub struct VM {
    stack: Vec<Rc<Value>>,
    frames: Vec<Frame>,
}

impl VM {
    pub fn new() -> Self { Self{ stack: Vec::new(), frames: Vec::new() } }

    fn push(&mut self, v: Value) { self.stack.push(Rc::new(v)); }
    fn pop(&mut self) -> Rc<Value> { self.stack.pop().unwrap_or_else(|| Rc::new(Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error", "stack")), message: "underflow".into(), payload: Value::Nil })))) }

    fn current_mut(&mut self) -> &mut Frame { self.frames.last_mut().expect("no frame") }

    pub fn call_main(&mut self, module: Rc<Module>, export: &Symbol) -> Value {
        let idx = *module.exports.get(&Rc::new(export.clone())).unwrap_or(&0);
        let clos = Closure::new(module.clone(), idx, vec![]);
        self.apply_closure(Rc::new(clos), &[])
    }

    fn load_u16(code: &[u8], ip: &mut usize) -> u16 { let v = u16::from_be_bytes([code[*ip], code[*ip+1]]); *ip += 2; v }
    fn load_i16(code: &[u8], ip: &mut usize) -> i16 { let v = i16::from_be_bytes([code[*ip], code[*ip+1]]); *ip += 2; v }

    fn value_eq(a: &Value, b: &Value) -> bool {
        match (a,b) {
            (Value::Int(x), Value::Int(y)) => x==y,
            (Value::Str(x), Value::Str(y)) => x==y,
            (Value::Bytes(x), Value::Bytes(y)) => x==y,
            (Value::Sym(x), Value::Sym(y)) => x.id == y.id,
            (Value::Nil, Value::Nil) => true,
            (Value::Pair(ax, ad), Value::Pair(bx, bd)) => Self::value_eq(ax, bx) && Self::value_eq(ad, bd),
            (Value::Error(ex), Value::Error(ey)) => ex.code.id == ey.code.id && ex.message == ey.message && Self::value_eq(&ex.payload, &ey.payload),
            (Value::Closure(cx), Value::Closure(cy)) => cx.code_hash == cy.code_hash && cx.env_shape_hash == cy.env_shape_hash,
            _ => false,
        }
    }

    fn as_int(v: &Value) -> Result<BigInt> { if let Value::Int(n)=v { Ok(n.clone()) } else { Err(anyhow!("type:int")) } }

    fn apply_primitive(&mut self, op: Op) {
        use Value::*;
        let err = |code:&str, msg:&str, payload:Value| -> Value { Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error", code)), message: msg.into(), payload })) };
        match op {
            Op::Cons => {
                let d = self.pop(); let a = self.pop(); self.push(Pair(a, d));
            }
            Op::Car => {
                let p = self.pop(); match &*p { Pair(a, _) => self.stack.push(a.clone()), _ => self.push(err("type","car expects pair", (*p).clone())) }
            }
            Op::Cdr => {
                let p = self.pop(); match &*p { Pair(_, d) => self.stack.push(d.clone()), _ => self.push(err("type","cdr expects pair", (*p).clone())) }
            }
            Op::NullP => { let x=self.pop(); self.push(Int(if matches!(&*x, Nil) { BigInt::one() } else { BigInt::zero() })); }
            Op::PairP => { let x=self.pop(); self.push(Int(if matches!(&*x, Pair(_, _)) { BigInt::one() } else { BigInt::zero() })); }
            Op::IntP => { let x=self.pop(); self.push(Int(if matches!(&*x, Int(_)) { BigInt::one() } else { BigInt::zero() })); }
            Op::StrP => { let x=self.pop(); self.push(Int(if matches!(&*x, Str(_)) { BigInt::one() } else { BigInt::zero() })); }
            Op::SymP => { let x=self.pop(); self.push(Int(if matches!(&*x, Sym(_)) { BigInt::one() } else { BigInt::zero() })); }
            Op::BytesP => { let x=self.pop(); self.push(Int(if matches!(&*x, Bytes(_)) { BigInt::one() } else { BigInt::zero() })); }
            Op::ClosP => { let x=self.pop(); self.push(Int(if matches!(&*x, Closure(_)) { BigInt::one() } else { BigInt::zero() })); }
            Op::ErrP => { let x=self.pop(); self.push(Int(if matches!(&*x, Error(_)) { BigInt::one() } else { BigInt::zero() })); }
            Op::Eq => {
                let b=self.pop(); let a=self.pop();
                let eq = match (&*a,&*b) { (Sym(x), Sym(y)) => x.id==y.id, (Int(x), Int(y)) => x==y, (Str(x), Str(y)) => x==y, (Bytes(x), Bytes(y)) => x==y, _ => false };
                self.push(Int(if eq { BigInt::one() } else { BigInt::zero() }));
            }
            Op::Equal => { let b=self.pop(); let a=self.pop(); self.push(Int(if Self::value_eq(&a, &b) { BigInt::one() } else { BigInt::zero() })); }
            Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Mod | Op::Abs | Op::Neg | Op::Cmp | Op::Shl | Op::Shr | Op::BAnd | Op::BOr | Op::BXor | Op::BNot => {
                // Numeric core
                match op {
                    Op::Abs => { let a=self.pop(); match &*a { Int(n)=> self.push(Int(n.abs())), _=> self.push(err("type","abs expects int", (*a).clone())) } }
                    Op::Neg => { let a=self.pop(); match &*a { Int(n)=> self.push(Int(-n.clone())), _=> self.push(err("type","neg expects int", (*a).clone())) } }
                    Op::BNot => { let a=self.pop(); match &*a { Int(n)=> { // bit-not: two's complement infinite
                        // ~x = -x - 1
                        self.push(Int((-n.clone()) - BigInt::one()));
                    }, _=> self.push(err("type","bnot expects int", (*a).clone())) } }
                    _ => {
                        let b=self.pop(); let a=self.pop();
                        let ai = Self::as_int(&a); let bi = Self::as_int(&b);
                        if let (Ok(a), Ok(b)) = (ai, bi) {
                            let v = match op {
                                Op::Add => a + b,
                                Op::Sub => a - b,
                                Op::Mul => a * b,
                                Op::Div => { if b.is_zero() { self.push(err("domain","div by zero", Value::Pair(Rc::new((*a).clone()), Rc::new((*b).clone())))); return; } // Euclidean floor toward -inf
                                    let (q, r) = a.div_rem(&b);
                                    // In Rust BigInt, div_rem is truncated toward zero. We need floor toward -inf.
                                    let needs_fix = ((a.sign()==Sign::Minus) ^ (b.sign()==Sign::Minus)) && !r.is_zero();
                                    let q = if needs_fix { q - BigInt::one() } else { q };
                                    q
                                }
                                Op::Mod => { if b.is_zero() { self.push(err("domain","mod by zero", Value::Pair(Rc::new((*a).clone()), Rc::new((*b).clone())))); return; }
                                    let (q, r0) = a.div_rem(&b);
                                    let needs_fix = ((a.sign()==Sign::Minus) ^ (b.sign()==Sign::Minus)) && !r0.is_zero();
                                    let r = if needs_fix { r0 + b } else { r0 };
                                    // ensure 0 <= r < |b|
                                    r
                                }
                                Op::Cmp => { if a < b { BigInt::from(-1) } else if a > b { BigInt::one() } else { BigInt::zero() } }
                                Op::Shl => { // n>=0
                                    if b.sign()==Sign::Minus { self.push(err("domain","shl negative shift", (*b).clone())); return; }
                                    let k = b.to_usize().unwrap_or(usize::MAX/2); a << k
                                }
                                Op::Shr => {
                                    if b.sign()==Sign::Minus { self.push(err("domain","shr negative shift", (*b).clone())); return; }
                                    let k = b.to_usize().unwrap_or(usize::MAX/2);
                                    // Arithmetic shift right: floor(a / 2^k) toward -inf
                                    if k==0 { a } else {
                                        // Use div with 2^k
                                        let two = BigInt::from(2u32);
                                        let pow = two.pow(k as u32);
                                        // floor div
                                        let (q, r) = a.div_rem(&pow);
                                        let needs_fix = a.sign()==Sign::Minus && !r.is_zero();
                                        if needs_fix { q - BigInt::one() } else { q }
                                    }
                                }
                                Op::BAnd => { // emulate bit ops via two's complement width = max(bitlen(a), bitlen(b))
                                    bitop_and(&a, &b)
                                }
                                Op::BOr => bitop_or(&a, &b),
                                Op::BXor => bitop_xor(&a, &b),
                                _ => unreachable!(),
                            };
                            self.push(Int(v));
                        } else {
                            self.push(err("type","numeric op expects ints", Value::Pair(a, b)));
                        }
                    }
                }
            }
            Op::StrLen => { let s=self.pop(); match &*s { Value::Str(st)=> self.push(Value::Int(BigInt::from(st.chars().count()))), _=> self.push(err("type","strlen expects string", (*s).clone())) } }
            Op::StrCat => { let b=self.pop(); let a=self.pop(); match (&*a,&*b) { (Value::Str(x), Value::Str(y)) => self.push(Value::Str(format!("{}{}", x,y))), _=> self.push(err("type","strcat expects strings", Value::Pair(a,b))) } }
            Op::BtLen => { let s=self.pop(); match &*s { Value::Bytes(bt)=> self.push(Value::Int(BigInt::from(bt.len()))), _=> self.push(err("type","bytes-len expects bytes", (*s).clone())) } }
            Op::BtSlice => { let j=self.pop(); let i=self.pop(); let b=self.pop(); match (&*b, Self::as_int(&i), Self::as_int(&j)) { (Value::Bytes(bytes), Ok(ii), Ok(jj)) => {
                    let (ii, jj) = (ii.to_usize().unwrap_or(0), jj.to_usize().unwrap_or(0));
                    if ii>jj || jj>bytes.len() { self.push(err("bounds","slice", (*b).clone())); } else { self.push(Value::Bytes(bytes[ii..jj].to_vec())); }
                }, _ => self.push(err("type","bytes-slice expects bytes,int,int", Value::Pair(b, Rc::new(Value::Pair(Rc::new((*i).clone()), Rc::new((*j).clone())))))) }
            }
            Op::Utf8Enc => { let s=self.pop(); match &*s { Value::Str(st)=> self.push(Value::Bytes(st.as_bytes().to_vec())), _=> self.push(err("type","utf8-encode expects string", (*s).clone())) } }
            Op::Utf8Dec => { let b=self.pop(); match &*b { Value::Bytes(bt)=> match std::str::from_utf8(bt) { Ok(s)=> self.push(Value::Str(s.to_string())), Err(_)=> self.push(err("encoding","invalid utf8", (*b).clone())) }, _=> self.push(err("type","utf8-decode expects bytes", (*b).clone())) } }
            Op::Sym => { let name=self.pop(); let pkg=self.pop(); match (&*pkg,&*name) { (Value::Str(p), Value::Str(n)) => self.push(Value::Sym(Rc::new(Symbol::new(p.clone(), n.clone())))), _=> self.push(err("type","sym expects strings", Value::Pair(pkg,name))) } }
            Op::SymName => { let s=self.pop(); match &*s { Value::Sym(sym)=> self.push(Value::Str(sym.name.clone())), _=> self.push(err("type","sym-name expects symbol", (*s).clone())) } }
            Op::SymPkg => { let s=self.pop(); match &*s { Value::Sym(sym)=> self.push(Value::Str(sym.package.clone())), _=> self.push(err("type","sym-package expects symbol", (*s).clone())) } }
            Op::Raise => { let x=self.pop(); match &*x { Value::Error(_)=> self.stack.push(x.clone()), _=> self.push(Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error","raised")), message:"raised".into(), payload:(*x).clone()}))) } }
            Op::IsErr => { let x=self.pop(); self.push(Value::Int(if matches!(&*x, Value::Error(_)) { BigInt::one() } else { BigInt::zero() })); }
            Op::ErrNew => { let pay=self.pop(); let msg=self.pop(); let code=self.pop(); match (&*code, &*msg) { (Value::Sym(c), Value::Str(m)) => self.push(Value::Error(Box::new(ErrorVal{ code: c.clone(), message: m.clone(), payload: (*pay).clone() }))), _=> self.push(err("type","error expects (sym str any)", Value::Pair(code, Rc::new(Value::Pair(msg, pay))))) } }
            Op::ErrCode => { let e=self.pop(); match &*e { Value::Error(ev)=> self.push(Value::Sym(ev.code.clone())), _=> self.push(err("type","error-code expects error", (*e).clone())) } }
            Op::ErrMsg => { let e=self.pop(); match &*e { Value::Error(ev)=> self.push(Value::Str(ev.message.clone())), _=> self.push(err("type","error-msg expects error", (*e).clone())) } }
            Op::ErrPayload => { let e=self.pop(); match &*e { Value::Error(ev)=> self.push(ev.payload.clone()), _=> self.push(err("type","error-payload expects error", (*e).clone())) } }
            Op::Hash => { let v=self.pop(); self.push(Value::Bytes(v.hash32().to_vec())); }
            Op::Encode => { let v=self.pop(); self.push(Value::Bytes(v.encode())); }
            Op::Decode => { let b=self.pop(); match &*b { Value::Bytes(bytes)=> match Value::decode(bytes) { Ok((v,_))=> self.push(v), Err(e)=> self.push(err("decode", &e.to_string(), (*b).clone())) }, _=> self.push(err("type","decode expects bytes", (*b).clone())) } }
            _ => {
                // Control, env and others are handled elsewhere; unknown → error
                self.push(Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error","bytecode")), message: format!("unimplemented op {op:?}"), payload: Value::Nil })));
            }
        }
    }

    fn apply_closure(&mut self, clos: Rc<Closure>, args: &[Rc<Value>]) -> Value {
        let func = &clos.module.functions[clos.func_idx as usize];
        if args.len() != func.arity as usize {
            return Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error","arity")), message: "arity".into(), payload: Value::Int(BigInt::from(args.len() as i32)) }));
        }
        // New frame
        let mut locals = Vec::with_capacity(func.nlocals as usize);
        for a in args { locals.push(a.clone()); }
        while locals.len() < func.nlocals as usize { locals.push(Rc::new(Value::Nil)); }
        let env_chain = vec![clos.env.clone()];
        self.frames.push(Frame{ module: clos.module.clone(), func_idx: clos.func_idx, ip: 0, locals, env: env_chain });
        // Run
        let result = self.run_current();
        result
    }

    fn run_current(&mut self) -> Value {
        loop {
            if self.frames.is_empty() { return Value::Nil; }
            let (module, func_idx, ip) = {
                let fr = self.frames.last().unwrap();
                (fr.module.clone(), fr.func_idx, fr.ip)
            };
            let func = &module.functions[func_idx as usize];
            if ip >= func.code.len() { return Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error","ip")), message:"ip past end".into(), payload: Value::Nil })); }
            let mut ip = ip;
            let op = unsafe { std::mem::transmute::<u8, Op>(func.code[ip]) }; ip += 1;
            // Save back ip by default; some ops will override
            self.frames.last_mut().unwrap().ip = ip;
            match op {
                Op::Nop => {}
                Op::Halt => { let v = self.pop(); self.frames.clear(); return (*v).clone(); }
                Op::Const => { let k = Self::load_u16(&func.code, &mut ip); self.frames.last_mut().unwrap().ip = ip; let v = module.consts[k as usize].clone(); self.push(v); }
                Op::LRef => {
                    let depth = Self::load_u16(&func.code, &mut ip) as usize;
                    let index = Self::load_u16(&func.code, &mut ip) as usize;
                    self.frames.last_mut().unwrap().ip = ip;
                    if depth == 0 {
                        // local
                        let v = self.frames.last().unwrap().locals.get(index).cloned().unwrap_or_else(|| Rc::new(Value::Nil));
                        self.stack.push(v);
                    } else {
                        // captured
                        let env = &self.frames.last().unwrap().env;
                        if depth-1 >= env.len() { self.push(Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error","env")), message:"bad depth".into(), payload: Value::Nil }))); }
                        else {
                            let cell = env[depth-1].get(index).cloned().unwrap_or_else(|| Rc::new(Value::Nil));
                            self.stack.push(cell);
                        }
                    }
                }
                Op::GRef => {
                    // Resolve global by export index order — for simplicity we assume a const Sym was pushed then GRef resolves it; in fuller linker we'd map indices.
                    // Here: GRef k => push export function as Closure with empty env.
                    let k = Self::load_u16(&func.code, &mut ip); self.frames.last_mut().unwrap().ip = ip;
                    let func_idx = k; // simple model
                    let clos = Closure::new(module.clone(), func_idx, vec![]);
                    self.stack.push(Rc::new(Value::Closure(Rc::new(clos))));
                }
                Op::Clos => {
                    let fidx = Self::load_u16(&func.code, &mut ip); let nfree = Self::load_u16(&func.code, &mut ip) as usize; self.frames.last_mut().unwrap().ip = ip;
                    let mut captured = Vec::with_capacity(nfree);
                    for _ in 0..nfree { let v = self.pop(); captured.push(v); }
                    captured.reverse();
                    let clos = Closure::new(module.clone(), fidx, captured);
                    self.stack.push(Rc::new(Value::Closure(Rc::new(clos))));
                }
                Op::Pop => { let _ = self.pop(); }
                Op::Call | Op::TCall => {
                    let nargs = Self::load_u16(&func.code, &mut ip) as usize; self.frames.last_mut().unwrap().ip = ip;
                    // collect args
                    let mut args = Vec::with_capacity(nargs);
                    for _ in 0..nargs { args.push(self.pop()); }
                    args.reverse();
                    let f = self.pop();
                    match &*f {
                        Value::Closure(c) => {
                            if op == Op::TCall {
                                // Replace current frame (tail-call)
                                let callee = &c.module.functions[c.func_idx as usize];
                                if nargs != callee.arity as usize {
                                    self.push(Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error","arity")), message:"arity".into(), payload: Value::Nil })));
                                } else {
                                    let mut locals = Vec::with_capacity(callee.nlocals as usize);
                                    for a in &args { locals.push(a.clone()); }
                                    while locals.len() < callee.nlocals as usize { locals.push(Rc::new(Value::Nil)); }
                                    let env_chain = vec![c.env.clone()];
                                    let top = self.frames.last_mut().unwrap();
                                    top.module = c.module.clone();
                                    top.func_idx = c.func_idx; top.ip = 0; top.locals = locals; top.env = env_chain;
                                }
                            } else {
                                let res = self.apply_closure(c.clone(), &args);
                                self.push(res);
                            }
                        }
                        other => {
                            // Primitive application not via CALL; use opcodes for primitives. If attempted, return error value.
                            self.push(Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error","apply")), message:"apply non-closure".into(), payload:(*other).clone() })));
                        }
                    }
                }
                Op::Ret => {
                    let v = self.pop();
                    let _ = self.frames.pop();
                    if self.frames.is_empty() { return (*v).clone(); }
                    else { self.stack.push(v); }
                }
                Op::IfJ => {
                    let off = Self::load_i16(&func.code, &mut ip);
                    // test top of stack
                    let test = self.pop();
                    let falsey = matches!(&*test, Value::Nil) || matches!(&*test, Value::Int(n) if n.is_zero());
                    if falsey {
                        let new_ip = (ip as isize) + (off as isize);
                        if new_ip < 0 || new_ip as usize > func.code.len() { return Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error","jump")), message:"ifj target".into(), payload: Value::Nil })); }
                        self.frames.last_mut().unwrap().ip = new_ip as usize;
                    } else { self.frames.last_mut().unwrap().ip = ip; }
                }
                Op::Jump => {
                    let off = Self::load_i16(&func.code, &mut ip);
                    let new_ip = (ip as isize) + (off as isize);
                    if new_ip < 0 || new_ip as usize > func.code.len() { return Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error","jump")), message:"target".into(), payload: Value::Nil })); }
                    self.frames.last_mut().unwrap().ip = new_ip as usize;
                }
                // Primitive opcodes
                op if matches!(op,
                    Op::Cons|Op::Car|Op::Cdr|Op::NullP|Op::PairP|Op::IntP|Op::StrP|Op::SymP|Op::BytesP|Op::ClosP|Op::ErrP|Op::Eq|Op::Equal|
                    Op::Add|Op::Sub|Op::Mul|Op::Div|Op::Mod|Op::Abs|Op::Neg|Op::Cmp|Op::Shl|Op::Shr|Op::BAnd|Op::BOr|Op::BXor|Op::BNot|
                    Op::StrLen|Op::StrRef|Op::StrCat|Op::BtLen|Op::BtRef|Op::BtSlice|Op::Utf8Enc|Op::Utf8Dec|
                    Op::Sym|Op::SymName|Op::SymPkg|
                    Op::Raise|Op::IsErr|Op::ErrNew|Op::ErrCode|Op::ErrMsg|Op::ErrPayload|
                    Op::Hash|Op::Encode|Op::Decode) => {
                    self.apply_primitive(op);
                }
                _ => {
                    // Push error value and continue
                    self.push(Value::Error(Box::new(ErrorVal{ code: Rc::new(Symbol::new("error","bytecode")), message: format!("unknown or unimpl op {op:?}"), payload: Value::Nil })));
                }
            }
        }
    }
}

// ------- Bitwise helpers with minimal-width two's-complement -------
fn bit_width(n: &BigInt) -> usize {
    if n.is_zero() { 1 } else { n.bits() as usize + 1 } // include sign bit
}
fn to_twos_width(n: &BigInt, w: usize) -> BigInt {
    // Clamp to width w in two's complement arithmetic
    if w == 0 { return BigInt::zero(); }
    let one = BigInt::one();
    let two = &one + &one;
    let modv = two.pow(w as u32);
    let mut x = n.mod_floor(&modv); // 0..2^w-1
    // Interpret as signed
    let half = two.pow((w-1) as u32);
    if x >= half { x -= modv; }
    x
}
fn choose_width(a:&BigInt, b:&BigInt) -> usize { bit_width(a).max(bit_width(b)) }
fn bitop_and(a:&BigInt, b:&BigInt) -> BigInt {
    let w = choose_width(a,b);
    let (ab, bb) = (be_twos_complement_from_bigint(a), be_twos_complement_from_bigint(b));
    let aw = to_fixed_width(&ab, w); let bw = to_fixed_width(&bb, w);
    let mut out = vec![0u8; aw.len()];
    for i in 0..aw.len() { out[i] = aw[i] & bw[i]; }
    be_twos_complement_to_bigint(&out)
}
fn bitop_or(a:&BigInt, b:&BigInt) -> BigInt {
    let w = choose_width(a,b);
    let aw = to_fixed_width(&be_twos_complement_from_bigint(a), w);
    let bw = to_fixed_width(&be_twos_complement_from_bigint(b), w);
    let mut out = vec![0u8; aw.len()];
    for i in 0..aw.len() { out[i] = aw[i] | bw[i]; }
    be_twos_complement_to_bigint(&out)
}
fn bitop_xor(a:&BigInt, b:&BigInt) -> BigInt {
    let w = choose_width(a,b);
    let aw = to_fixed_width(&be_twos_complement_from_bigint(a), w);
    let bw = to_fixed_width(&be_twos_complement_from_bigint(b), w);
    let mut out = vec![0u8; aw.len()];
    for i in 0..aw.len() { out[i] = aw[i] ^ bw[i]; }
    be_twos_complement_to_bigint(&out)
}
fn to_fixed_width(be: &[u8], w_bits: usize) -> Vec<u8> {
    // Ensure exactly w_bits two's complement width
    let bytes = (w_bits + 7) / 8;
    let neg = (be[0] & 0x80) != 0;
    let mut out = vec![if neg {0xFF} else {0x00}; bytes];
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
    let consts = vec![ Value::Int(1.into()), Value::Int(2.into()), Value::Int(3.into()) ];
    // code: CONST 0; CONST 1; ADD; CONST 2; MUL; HALT
    let mut code = Vec::new();
    code.push(Op::Const as u8); code.extend_from_slice(&0u16.to_be_bytes());
    code.push(Op::Const as u8); code.extend_from_slice(&1u16.to_be_bytes());
    code.push(Op::Add as u8);
    code.push(Op::Const as u8); code.extend_from_slice(&2u16.to_be_bytes());
    code.push(Op::Mul as u8);
    code.push(Op::Halt as u8);
    let func = Function{ arity: 0, nlocals: 0, code };
    let mut exports = BTreeMap::new();
    exports.insert(Rc::new(Symbol::new("user","main")), 0);
    Rc::new(Module::new(consts, vec![func], exports))
}

fn main() {
    let module = build_demo_module();
    let mut vm = VM::new();
    let result = vm.call_main(module.clone(), &Symbol::new("user","main"));
    println!("Result: {result:?}");
}
