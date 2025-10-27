use super::*;
use std::collections::HashMap;
use std::rc::Rc;

#[test]
fn canonical_primitives() {
    assert_eq!(Value::Nil.to_canonical(), "()");
    assert_eq!(Value::Int(42.into()).to_canonical(), "42");
    assert_eq!(Value::Str("hi\n\"".into()).to_canonical(), "\"hi\\n\\\"\"");
    let sym = Rc::new(Symbol::new("core", "lambda"));
    assert_eq!(Value::Sym(sym).to_canonical(), "core/lambda");
    assert_eq!(Value::Bytes(vec![1, 2, 255]).to_canonical(), "#u8(1 2 255)");
}

#[test]
fn reader_basic_atoms() {
    let forms = read_all("42 'x \"hi\"").expect("read");
    assert_eq!(forms.len(), 3);
    assert!(matches!(forms[0], Value::Int(ref n) if n == &BigInt::from(42)));
    assert_eq!(forms[1].to_canonical(), "(quote x)");
    assert_eq!(forms[2].to_canonical(), "\"hi\"");
}

#[test]
fn reader_bytes_and_symbols() {
    let src = "#u8(1 2 3) foo/bar |pkg name|/|sym+|";
    let forms = read_all(src).expect("read");
    assert_eq!(forms.len(), 3);
    match &forms[0] {
        Value::Bytes(bytes) => assert_eq!(bytes, &vec![1, 2, 3]),
        other => panic!("unexpected {other:?}"),
    }
    match &forms[1] {
        Value::Sym(sym) => {
            assert_eq!(sym.package, "foo");
            assert_eq!(sym.name, "bar");
        }
        _ => panic!("expected symbol"),
    }
    match &forms[2] {
        Value::Sym(sym) => {
            assert_eq!(sym.package, "pkg name");
            assert_eq!(sym.name, "sym+");
        }
        _ => panic!("expected quoted symbol"),
    }
}

#[test]
fn canonical_symbol_quoting() {
    let sym = Rc::new(Symbol::new("user", "has space"));
    assert_eq!(Value::Sym(sym).to_canonical(), "|has space|");
    let pkg_sym = Rc::new(Symbol::new("pkg", "weird|name"));
    assert_eq!(Value::Sym(pkg_sym).to_canonical(), "pkg/|weird\\|name|");
}

#[test]
fn canonical_lists() {
    let list = Value::Pair(
        Rc::new(Value::Int(1.into())),
        Rc::new(Value::Pair(
            Rc::new(Value::Int(2.into())),
            Rc::new(Value::Nil),
        )),
    );
    assert_eq!(list.to_canonical(), "(1 2)");

    let dotted = Value::Pair(Rc::new(Value::Int(1.into())), Rc::new(Value::Int(2.into())));
    assert_eq!(dotted.to_canonical(), "(1 . 2)");
}

#[test]
fn canonical_error_and_closure() {
    let err = Value::Error(Box::new(ErrorVal {
        code: Rc::new(Symbol::new("error", "arity")),
        message: "wrong arity".into(),
        payload: Value::Nil,
    }));
    assert_eq!(err.to_canonical(), "#<error error/arity:wrong arity>");

    let clo = Value::Closure(Rc::new(Closure::opaque([0xAA; 32], [0x55; 32])));
    assert_eq!(
        clo.to_canonical(),
        format!(
            "#<closure code={} env={}>",
            "aa".repeat(32),
            "55".repeat(32)
        )
    );
}

struct DummyResolver {
    modules: HashMap<[u8; 32], Rc<Module>>,
}

impl DummyResolver {
    fn new(modules: Vec<Rc<Module>>) -> Self {
        let mut map = HashMap::new();
        for module in modules {
            map.insert(module.hash, module);
        }
        Self { modules: map }
    }
}

impl ModuleResolver for DummyResolver {
    fn resolve(&self, hash: &[u8; 32]) -> Option<Rc<Module>> {
        self.modules.get(hash).cloned()
    }
}

#[test]
fn snapshot_round_trip_vm() {
    let shared = Rc::new(Value::Bytes(vec![1, 2, 3]));
    let sym = Rc::new(Symbol::new("user", "token"));
    let module = Rc::new(Module::new(
        vec![],
        vec![Function {
            arity: 0,
            nlocals: 0,
            code: vec![Op::Ret as u8],
        }],
        vec![],
    ));
    let closure = Closure::new(module.clone(), 0, vec![shared.clone()]);

    let mut vm = VM::new();
    vm.push_rc(shared.clone());
    vm.push_rc(Rc::new(Value::Sym(sym.clone())));
    vm.push_rc(Rc::new(Value::Closure(Rc::new(closure))));
    vm.push_frame(Frame::new_for_test(
        module.clone(),
        0,
        0,
        vec![shared.clone()],
        vec![vec![shared.clone()]],
    ));

    let snapshot = vm.snapshot().expect("snapshot");
    let encoded = snapshot.encode().expect("encode");
    let decoded = Snapshot::decode(&encoded).expect("decode");
    let resolver = DummyResolver::new(vec![module.clone()]);
    let restored = VM::restore(&decoded, &resolver).expect("restore");

    let stack = restored.stack_ref();
    assert_eq!(stack.len(), 3);
    assert!(matches!(&*stack[1], Value::Sym(_)));
    if let Value::Closure(c) = stack[2].as_ref() {
        assert!(Rc::ptr_eq(&c.env[0], &stack[0]));
    } else {
        panic!("expected closure");
    }

    let frames = restored.frames_ref();
    assert_eq!(frames.len(), 1);
    let frame = &frames[0];
    assert_eq!(frame.func_idx, 0);
    assert!(Rc::ptr_eq(&frame.locals_ref()[0], &stack[0]));
}

#[test]
fn snapshot_digest_guard() {
    let vm = VM::new();
    let snapshot = vm.snapshot().expect("snapshot");
    let mut encoded = snapshot.encode().expect("encode");
    let last = encoded.last_mut().expect("digest");
    *last ^= 0xFF;
    assert!(Snapshot::decode(&encoded).is_err());
}
