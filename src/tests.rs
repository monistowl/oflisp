use super::*;
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
