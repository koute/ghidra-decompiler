use std::io::Cursor;

use ghidra_decompiler::address::Address;
use ghidra_decompiler::architecture::{Architecture, ArchitectureCapability, ErrorStream};
use ghidra_decompiler::database::{Database, SymbolId, SymbolKind};
use ghidra_decompiler::funcdata::Funcdata;
use ghidra_decompiler::grammar::parse_type;
use ghidra_decompiler::op::PcodeOp;
use ghidra_decompiler::opcodes::OpCode;
use ghidra_decompiler::typeop::with_type_op;
use ghidra_decompiler::types::{EnumRepresentation, TypeId, TypeMetatype};
use ghidra_decompiler::xml::DocumentStorage;
use ghidra_decompiler::xml_arch::XML_ARCHITECTURE_CAPABILITY;

struct TypeTestEnvironment {
    glb: Box<Architecture>,
    dummy_func: Option<Box<Funcdata>>,
    dummy_symbol: SymbolId,
}

impl TypeTestEnvironment {
    fn build() -> TypeTestEnvironment {
        let mut store = DocumentStorage::new();
        let doc = store
            .parse_document(b"<binaryimage arch=\"x86:LE:64:default:gcc\"></binaryimage>")
            .expect("invalid binaryimage document");
        store.register_tag(doc.get_root());
        let estream: ErrorStream = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
        let mut glb = XML_ARCHITECTURE_CAPABILITY
            .build_architecture("", "", Some(estream))
            .expect("xml architecture construction failed");
        glb.init(&mut store).expect("architecture initialization failed");
        let codespace = glb
            .manager
            .get_default_code_space()
            .expect("missing default code space");
        let addr = Address::new(codespace, 0x1000);
        let global = glb
            .symboltab
            .as_ref()
            .and_then(|symboltab| symboltab.get_global_scope())
            .expect("missing global scope");
        let dummy_symbol =
            Database::scope_add_function(&mut glb, global, &addr, "dummy").expect("function creation failed");
        Database::symbol_get_function(&mut glb, dummy_symbol).expect("missing function data");
        let mut dummy_func = take_function(&mut glb, dummy_symbol);
        dummy_func.set_high_level(&mut glb).expect("high level setup failed");
        TypeTestEnvironment {
            glb,
            dummy_func: Some(dummy_func),
            dummy_symbol,
        }
    }

    fn parse(&mut self, text: &str) -> TypeId {
        let mut stream = Cursor::new(text.as_bytes().to_vec());
        let mut unused = String::new();
        parse_type(&mut stream, &mut unused, &mut self.glb).expect("type parse failed")
    }

    fn size_of(&self, tp: TypeId) -> i32 {
        self.glb
            .types
            .as_ref()
            .expect("missing type factory")
            .get(tp)
            .get_size()
    }

    fn cast_printed(&mut self, opc: OpCode, first: TypeId, second: TypeId) -> bool {
        let first_size = self.size_of(first);
        let second_size = self.size_of(second);
        let codespace = self
            .glb
            .manager
            .get_default_code_space()
            .expect("missing default code space");
        let addr = Address::new(codespace, 0x1000);
        let flags = self.glb.inst[opc.index()]
            .as_ref()
            .expect("missing type op")
            .get_flags();
        let mut fd = self.dummy_func.take().expect("missing dummy function");
        let glb = &mut self.glb;
        let op;
        if (flags & PcodeOp::UNARY) != 0 {
            op = fd.new_op(1, &addr);
            let vn1 = fd.new_unique(second_size, Some(second), glb);
            let outvn = fd.new_unique_out(first_size, op, glb).expect("output creation failed");
            fd.vn_update_type_locked(outvn, first, true, true, glb);
            fd.op_set_opcode(op, opc, glb);
            fd.op_set_input(op, vn1, 0).expect("input assignment failed");
        } else {
            op = fd.new_op(2, &addr);
            let vn1 = fd.new_unique(first_size, Some(first), glb);
            let vn2 = fd.new_unique(second_size, Some(second), glb);
            fd.op_set_opcode(op, opc, glb);
            fd.op_set_input(op, vn1, 0).expect("input assignment failed");
            fd.op_set_input(op, vn2, 1).expect("input assignment failed");
            fd.new_unique_out(1, op, glb).expect("output creation failed");
        }
        let printslot = glb.print;
        let print = glb.printlist[printslot].take().expect("missing print language");
        let strategy = print.get_cast_strategy().expect("missing cast strategy");
        let res = with_type_op(glb, opc, |top, glb| top.get_input_cast(op, 0, strategy, &mut fd, glb));
        glb.printlist[printslot] = Some(print);
        self.dummy_func = Some(fd);
        res.expect("cast query failed").is_some()
    }

    fn long_printed(&mut self, opc: OpCode, first: TypeId, val: u64) -> bool {
        let first_size = self.size_of(first);
        let codespace = self
            .glb
            .manager
            .get_default_code_space()
            .expect("missing default code space");
        let addr = Address::new(codespace, 0x1000);
        let mut fd = self.dummy_func.take().expect("missing dummy function");
        let glb = &mut self.glb;
        let op = fd.new_op(2, &addr);
        let shift = glb
            .types
            .as_mut()
            .expect("missing type factory")
            .get_base(4, TypeMetatype::Int)
            .expect("missing base type");
        let shift_size = glb.types.as_ref().expect("missing type factory").get(shift).get_size();
        let vn1 = fd.new_constant(first_size, val, glb);
        fd.vn_update_type_locked(vn1, first, false, true, glb);
        let vn2 = fd.new_unique(shift_size, Some(shift), glb);
        fd.op_set_opcode(op, opc, glb);
        fd.op_set_input(op, vn1, 0).expect("input assignment failed");
        fd.op_set_input(op, vn2, 1).expect("input assignment failed");
        let vn1_size = fd.vn(vn1).get_size();
        fd.new_unique_out(vn1_size, op, glb).expect("output creation failed");
        let printslot = glb.print;
        let print = glb.printlist[printslot].take().expect("missing print language");
        let res = print
            .get_cast_strategy()
            .expect("missing cast strategy")
            .mark_explicit_long_size(op, 0, &mut fd, glb);
        glb.printlist[printslot] = Some(print);
        self.dummy_func = Some(fd);
        res.expect("explicit long size check failed")
    }

    fn base_with_name(&mut self, size: i32, meta: TypeMetatype, name: &str) -> TypeId {
        self.glb
            .types
            .as_mut()
            .expect("missing type factory")
            .get_base_named(size, meta, name)
            .expect("missing base type with this name")
    }

    fn compare(&self, first: TypeId, second: TypeId) -> i32 {
        let types = self.glb.types.as_ref().expect("missing type factory");
        types.get(first).compare(types.get(second), 10, types)
    }

    fn compare_dependency(&self, first: TypeId, second: TypeId) -> i32 {
        let types = self.glb.types.as_ref().expect("missing type factory");
        types.get(first).compare_dependency(types.get(second), types)
    }

    fn matches(&self, tp: TypeId, val: u64, rep: &mut EnumRepresentation) {
        let types = self.glb.types.as_ref().expect("missing type factory");
        types.get(tp).get_matches(val, rep, types);
    }
}

impl Drop for TypeTestEnvironment {
    fn drop(&mut self) {
        if let Some(fd) = self.dummy_func.take()
            && let Some(symboltab) = self.glb.symboltab.as_mut()
            && let SymbolKind::Function { fd: slot, .. } = &mut symboltab.symbol_mut(self.dummy_symbol).kind
        {
            *slot = Some(fd);
        }
    }
}

fn take_function(glb: &mut Architecture, sym: SymbolId) -> Box<Funcdata> {
    let symboltab = glb.symboltab.as_mut().expect("missing symbol table");
    match &mut symboltab.symbol_mut(sym).kind {
        SymbolKind::Function { fd, .. } => fd.take().expect("function data is not built"),
        _ => panic!("symbol is not a function"),
    }
}

#[test]
fn cast_basic() {
    let mut env = TypeTestEnvironment::build();
    let (dst, src) = (env.parse("int4"), env.parse("int2"));
    assert!(env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("int4"), env.parse("uint4"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("int4 *"), env.parse("uint8"));
    assert!(env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("int1"), env.parse("bool"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("xunknown4"), env.parse("uint4"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("int4"), env.parse("xunknown4"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("int4"), env.parse("float4"));
    assert!(env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("int1 var[4]"), env.parse("uint4"));
    assert!(env.cast_printed(OpCode::Copy, dst, src));
    let typedef_int = env.base_with_name(4, TypeMetatype::Int, "myint4");
    let src = env.parse("int4");
    assert!(!env.cast_printed(OpCode::Copy, typedef_int, src));
    let (dst, src) = (env.parse("char"), env.parse("int1"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("uint1"), env.parse("char"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
}

#[test]
fn cast_pointer() {
    let mut env = TypeTestEnvironment::build();
    let (dst, src) = (env.parse("uint4 *"), env.parse("int4 *"));
    assert!(env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("void *"), env.parse("float4 *"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("int2 *"), env.parse("void *"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
    let typedef_int = env.base_with_name(4, TypeMetatype::Int, "myint4");
    let typedef_ptr = env
        .glb
        .types
        .as_mut()
        .expect("missing type factory")
        .get_type_pointer(8, typedef_int, 1)
        .expect("pointer creation failed");
    let src = env.parse("int4 *");
    assert!(!env.cast_printed(OpCode::Copy, typedef_ptr, src));
    let (dst, src) = (env.parse("bool **"), env.parse("int1 **"));
    assert!(env.cast_printed(OpCode::Copy, dst, src));
    env.parse("struct structone { int4 a; int4 b; }");
    env.parse("struct structtwo { int4 a; int4 b; }");
    let (dst, src) = (env.parse("structone *"), env.parse("structtwo *"));
    assert!(env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("xunknown4 *"), env.parse("int4 *"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("uint4 *"), env.parse("xunknown4 *"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("char *"), env.parse("int1 *"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
    let (dst, src) = (env.parse("uint1 *"), env.parse("char *"));
    assert!(env.cast_printed(OpCode::Copy, dst, src));
    let int4 = env.parse("int4");
    let ptr_with_name = env
        .glb
        .types
        .as_mut()
        .expect("missing type factory")
        .get_type_pointer_named(8, int4, 1, "myptrint4")
        .expect("pointer creation failed");
    let dst = env.parse("int4 *");
    assert!(!env.cast_printed(OpCode::Copy, dst, ptr_with_name));
}

#[test]
fn cast_enum() {
    let mut env = TypeTestEnvironment::build();
    let enum1 = env.parse("enum enumone { ONE=1, TWO=2 }");
    let dst = env.parse("int8");
    assert!(!env.cast_printed(OpCode::Copy, dst, enum1));
    let (dst, src) = (env.parse("uint8 *"), env.parse("enumone *"));
    assert!(!env.cast_printed(OpCode::Copy, dst, src));
    let src = env.parse("uint8");
    assert!(!env.cast_printed(OpCode::Copy, enum1, src));
}

#[test]
fn cast_compare() {
    let mut env = TypeTestEnvironment::build();
    let (first, second) = (env.parse("int4"), env.parse("int4"));
    assert!(env.cast_printed(OpCode::IntLess, first, second));
    let (first, second) = (env.parse("uint4"), env.parse("uint4"));
    assert!(!env.cast_printed(OpCode::IntLess, first, second));
    let (first, second) = (env.parse("int4 *"), env.parse("int4 *"));
    assert!(!env.cast_printed(OpCode::IntLess, first, second));
    let (first, second) = (env.parse("uint4"), env.parse("uint4"));
    assert!(env.cast_printed(OpCode::IntSless, first, second));
    let (first, second) = (env.parse("int4"), env.parse("int4"));
    assert!(!env.cast_printed(OpCode::IntSless, first, second));
    let (first, second) = (env.parse("uint8"), env.parse("int4 *"));
    assert!(env.cast_printed(OpCode::IntEqual, first, second));
    let (first, second) = (env.parse("int4 *"), env.parse("uint8"));
    assert!(!env.cast_printed(OpCode::IntEqual, first, second));
    let (first, second) = (env.parse("int4"), env.parse("uint4"));
    assert!(!env.cast_printed(OpCode::IntNotequal, first, second));
    let (first, second) = (env.parse("uint4"), env.parse("int4"));
    assert!(!env.cast_printed(OpCode::IntNotequal, first, second));
    let (first, second) = (env.parse("int4"), env.parse("float4"));
    assert!(env.cast_printed(OpCode::IntEqual, first, second));
}

#[test]
fn type_ordering() {
    let mut env = TypeTestEnvironment::build();
    let (first, second) = (env.parse("uint4"), env.parse("int4"));
    assert!(env.compare(first, second) < 0);
    let int_typedef = env.base_with_name(4, TypeMetatype::Int, "myint4");
    let int4 = env.parse("int4");
    assert_ne!(int4, int_typedef);
    assert!(env.compare_dependency(int4, int_typedef) == 0);
    let (first, second) = (env.parse("int1"), env.parse("char"));
    assert!(env.compare(first, second) < 0);
    let (first, second) = (env.parse("wchar2"), env.parse("int2"));
    assert!(env.compare(first, second) < 0);
    let (first, second) = (env.parse("wchar4"), env.parse("int4"));
    assert!(env.compare(first, second) < 0);
    let (first, second) = (env.parse("uint1"), env.parse("char"));
    assert!(env.compare(first, second) < 0);
    let enum1 = env.parse("enum enum2 { ONE=1, TWO=2 }");
    let int8 = env.parse("int8");
    assert!(env.compare(enum1, int8) < 0);
    let struct1 = env.parse("struct struct1 { int4 a; int4 b; }");
    let struct2 = env.parse("struct struct2 { int4 a; int4 b; }");
    assert_ne!(struct1, struct2);
    assert!(env.compare_dependency(struct1, struct2) == 0);
    let (first, second) = (env.parse("uint4"), env.parse("uint2"));
    assert!(env.compare(first, second) < 0);
    let (first, second) = (env.parse("float8"), env.parse("float4"));
    assert!(env.compare(first, second) < 0);
    let (first, second) = (env.parse("bool"), env.parse("uint1"));
    assert!(env.compare(first, second) < 0);
    let (first, second) = (env.parse("uint4 *"), env.parse("int4 *"));
    assert!(env.compare(first, second) < 0);
    let (first, second) = (env.parse("enum2 *"), env.parse("int8 *"));
    assert!(env.compare(first, second) < 0);
    let (first, second) = (env.parse("int4 *"), env.parse("void *"));
    assert!(env.compare(first, second) < 0);
    let (first, second) = (env.parse("int2 *"), env.parse("xunknown2 *"));
    assert!(env.compare(first, second) < 0);
}

#[test]
fn cast_integertoken() {
    let mut env = TypeTestEnvironment::build();
    let int8 = env.parse("int8");
    let uint8 = env.parse("uint8");
    assert!(env.long_printed(OpCode::IntLeft, int8, 10));
    assert!(!env.long_printed(OpCode::IntLeft, int8, 0x100000000));
    assert!(env.long_printed(OpCode::IntSright, int8, (-3i64) as u64));
    assert!(!env.long_printed(OpCode::IntSright, int8, 0xffffffff7fffffff));
    assert!(env.long_printed(OpCode::IntSright, int8, 0xffffffff80000000));
    assert!(env.long_printed(OpCode::IntRight, uint8, 0xffffffff));
    assert!(!env.long_printed(OpCode::IntRight, uint8, 0x100000000));
}

#[test]
fn enum_matching() {
    let mut env = TypeTestEnvironment::build();
    let enum3 = env.parse("enum enum3 { ZERO=0, ONE=1, TWO=2, FOUR=4, EIGHT=8 }");
    let mut rep = EnumRepresentation::new();
    env.matches(enum3, 5, &mut rep);
    assert!(rep.matchname.len() == 2);
    assert!(rep.matchname[0] == "FOUR");
    assert!(rep.matchname[1] == "ONE");
    assert!(!rep.complement);
    rep.matchname.clear();
    env.matches(enum3, 0xfffffffffffffff7, &mut rep);
    assert!(rep.matchname.len() == 1);
    assert!(rep.matchname[0] == "EIGHT");
    assert!(rep.complement);
    rep.matchname.clear();
    rep.complement = false;
    env.matches(enum3, 0, &mut rep);
    assert!(rep.matchname.len() == 1);
    assert!(rep.matchname[0] == "ZERO");
    assert!(!rep.complement);
    rep.matchname.clear();
    env.matches(enum3, 0x10, &mut rep);
    assert!(rep.matchname.is_empty());
    assert!(!rep.complement);
}

#[test]
fn enum_matching2() {
    let mut env = TypeTestEnvironment::build();
    let enum4 = env.parse("enum enum4 { ZERO=0, ONE=1, TWO=2, FOUR=4, SIX=6, EIGHT=8, ELEVEN=11 }");
    let mut rep = EnumRepresentation::new();
    env.matches(enum4, 12, &mut rep);
    assert!(rep.matchname.len() == 2);
    assert!(rep.matchname[0] == "EIGHT");
    assert!(rep.matchname[1] == "FOUR");
    assert!(!rep.complement);
    rep.matchname.clear();
    env.matches(enum4, 7, &mut rep);
    assert!(rep.matchname.len() == 2);
    assert!(rep.matchname[0] == "SIX");
    assert!(rep.matchname[1] == "ONE");
    assert!(!rep.complement);
    rep.matchname.clear();
    env.matches(enum4, 11, &mut rep);
    assert!(rep.matchname.len() == 1);
    assert!(rep.matchname[0] == "ELEVEN");
    assert!(!rep.complement);
}
