use std::io::Cursor;

use ghidra_decompiler::architecture::{Architecture, ArchitectureCapability, ErrorStream};
use ghidra_decompiler::fspec::{ModelId, ParameterPieces, PrototypePieces};
use ghidra_decompiler::grammar::{parse_c, parse_protopieces};
use ghidra_decompiler::istream::{Basefield, read_i32, read_u32, read_u64};
use ghidra_decompiler::pcoderaw::VarnodeData;
use ghidra_decompiler::types::TypeMetatype;
use ghidra_decompiler::xml::DocumentStorage;
use ghidra_decompiler::xml_arch::XML_ARCHITECTURE_CAPABILITY;

struct ParamStoreEnvironment {
    glb: Box<Architecture>,
}

impl ParamStoreEnvironment {
    fn build_arch(arch: &str) -> ParamStoreEnvironment {
        let mut store = DocumentStorage::new();
        let text = format!("<binaryimage arch=\"{arch}\"></binaryimage>");
        let doc = store
            .parse_document(text.as_bytes())
            .expect("invalid binaryimage document");
        store.register_tag(doc.get_root());
        let estream: ErrorStream = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
        let mut glb = XML_ARCHITECTURE_CAPABILITY
            .build_architecture("", "", Some(estream))
            .expect("xml architecture construction failed");
        glb.init(&mut store).expect("architecture initialization failed");
        ParamStoreEnvironment { glb }
    }

    fn get_model(&self, model: &str) -> ModelId {
        *self.glb.proto_model_map.get(model).expect("missing prototype model")
    }

    fn parse_type(&mut self, definition: &str) {
        let mut stream = Cursor::new(definition.as_bytes().to_vec());
        parse_c(&mut self.glb, &mut stream).expect("type definition parse failed");
    }

    fn test(&mut self, model: ModelId, signature: &str, stores: &str) -> bool {
        let mut stream = Cursor::new(signature.as_bytes().to_vec());
        let mut pieces = PrototypePieces::default();
        parse_protopieces(&mut pieces, &mut stream, &mut self.glb).expect("prototype parse failed");
        let mut res = Vec::new();
        let glb = &mut *self.glb;
        ghidra_decompiler::fspec::assign_storage_glb(model, &pieces, &mut res, false, glb)
            .expect("parameter storage assignment failed");
        let mut store_data = Vec::new();
        self.parse_stores(&mut store_data, stores);
        if store_data.len() != res.len() {
            return false;
        }
        for (data, piece) in store_data.iter().zip(res.iter()) {
            if !self.compare_piece(data, piece) {
                return false;
            }
        }
        true
    }

    fn parse_join(&self, join: &str) -> VarnodeData {
        let mut pieces = Vec::new();
        let mut pos = join.find(' ').map(|found| found + 1).unwrap_or(0);
        loop {
            let nextpos = join[pos..].find(' ').map(|found| found + pos);
            let element = match nextpos {
                None => &join[pos..],
                Some(next) => &join[pos..next],
            };
            pieces.push(self.parse_store(element));
            match nextpos {
                None => break,
                Some(next) => pos = next + 1,
            }
        }
        let size: u32 = if pieces.len() == 1 { 4 } else { 0 };
        self.glb
            .manager
            .find_add_join(&pieces, size)
            .expect("join record creation failed")
            .get_unified()
    }

    fn parse_store(&self, name: &str) -> VarnodeData {
        if name == "void" {
            return VarnodeData {
                space: None,
                offset: 0,
                size: 0,
            };
        }
        if name.starts_with("stack") {
            let pos = name.find(':');
            let end = match pos {
                Some(found) => (5 + found).min(name.len()),
                None => name.len(),
            };
            let mut res = VarnodeData {
                space: self.glb.manager.get_stack_space(),
                offset: read_u64(&name[5..end], Basefield::Hex, 0),
                size: 1,
            };
            if let Some(found) = pos {
                res.size = read_u32(&name[found + 1..], Basefield::Dec, res.size);
            }
            return res;
        } else if name.starts_with("join") {
            return self.parse_join(name);
        }
        let pos = name.find(':');
        let mut sz = 0;
        let regname = match pos {
            Some(found) => {
                sz = read_i32(&name[found + 1..], Basefield::Dec, sz);
                &name[..found]
            }
            None => name,
        };
        let mut res = self
            .glb
            .translate
            .as_ref()
            .expect("missing translator")
            .get_register(regname)
            .expect("unknown register");
        if sz != 0 {
            if res.space.as_ref().expect("register without space").is_big_endian() {
                res.offset += (res.size as i32 - sz) as u64;
            }
            res.size = sz as u32;
        }
        res
    }

    fn parse_stores(&self, res: &mut Vec<VarnodeData>, names: &str) {
        let mut pos = 0usize;
        loop {
            let nextpos = names[pos..].find(',').map(|found| found + pos);
            let element = match nextpos {
                None => &names[pos..],
                Some(next) => &names[pos..next],
            };
            res.push(self.parse_store(element));
            match nextpos {
                None => break,
                Some(next) => pos = next + 1,
            }
        }
    }

    fn compare_piece(&self, data: &VarnodeData, piece: &ParameterPieces) -> bool {
        let types = self.glb.types.as_ref().expect("missing type factory");
        let piece_type = types.get(piece.tp.expect("missing parameter type"));
        let Some(space) = &data.space else {
            return piece_type.get_metatype() == TypeMetatype::Void;
        };
        match piece.addr.get_space() {
            Some(piece_space) if piece_space.get_index() == space.get_index() => {}
            _ => return false,
        }
        if data.offset != piece.addr.get_offset() {
            return false;
        }
        data.size as i32 == piece_type.get_size()
    }
}

#[test]
fn paramstore_x64() {
    let mut env = ParamStoreEnvironment::build_arch("x86:LE:64:default:gcc");
    let model = env.get_model("__stdcall");
    assert!(env.test(model, "void func(int4,int4);", "void,EDI,ESI"));
    assert!(env.test(model, "void func(float4,float4);", "void,XMM0:4,XMM1:4"));
    assert!(env.test(model, "void func(int2 a,int4 b,int1 c);", "void,DI,ESI,DX:1"));
    assert!(env.test(model, "void func(int8,int8);", "void,RDI,RSI"));
    assert!(env.test(model, "void func(float8,float8);", "void,XMM0:8,XMM1:8"));
    assert!(env.test(
        model,
        "void func(int4,float4,int4,float4);",
        "void,EDI,XMM0:4,ESI,XMM1:4"
    ));
    assert!(env.test(
        model,
        "void func(float4,int4,float4,int4);",
        "void,XMM0:4,EDI,XMM1:4,ESI"
    ));
    assert!(env.test(
        model,
        "void func(int4,float8,float8,int4);",
        "void,EDI,XMM0:8,XMM1:8,ESI"
    ));
    assert!(env.test(
        model,
        "void func(float8,int8,int8,float8);",
        "void,XMM0:8,RDI,RSI,XMM1:8"
    ));
    assert!(env.test(model, "void func(float10);", "void,stack8:10"));
    assert!(env.test(
        model,
        "void func(float4,float10,float4);",
        "void,XMM0:4,stack8:10,XMM1:4"
    ));
    env.parse_type("struct intfloatpair { int4 a; float4 b;};");
    assert!(env.test(model, "void func(intfloatpair);", "void,RDI"));
    env.parse_type("struct longfloatpair { int8 a; float4 b;};");
    assert!(env.test(model, "void func(int4,longfloatpair);", "void,EDI,join XMM0:8 RSI"));
    env.parse_type("struct longdoublepair { int8 a; float8 b;};");
    assert!(env.test(model, "void func(int4,longdoublepair);", "void,EDI,join XMM0:8 RSI"));
    env.parse_type("struct intdoublepair { int4 a; float8 b;};");
    assert!(env.test(model, "void func(int4,intdoublepair);", "void,EDI,join XMM0:8 RSI"));
    env.parse_type("struct floatintpair { float4 a; int4 b;};");
    assert!(env.test(model, "void func(int4,floatintpair);", "void,EDI,RSI"));
    env.parse_type("struct doubleintpair { float8 a; int4 b;};");
    assert!(env.test(model, "void func(int4,doubleintpair);", "void,EDI,join RSI XMM0:8"));
    env.parse_type("struct intintfloat { int4 a; int4 b; float4 c; };");
    assert!(env.test(model, "void func(int4,intintfloat);", "void,EDI,join XMM0:4 RSI"));
    env.parse_type("struct intintfloatfloat { int4 a; int4 b; float4 c; float4 d;};");
    assert!(env.test(model, "void func(int4,intintfloatfloat);", "void,EDI,join XMM0:8 RSI"));
    env.parse_type("struct intfloatfloatint { int4 a; float4 b; float4 c; int4 d;};");
    assert!(env.test(model, "void func(int4,intfloatfloatint);", "void,EDI,join RDX RSI"));
    env.parse_type("struct intfloatfloat { int4 a; float4 b; float4 c; };");
    assert!(env.test(model, "void func(int4,intfloatfloat);", "void,EDI,join XMM0:4 RSI"));
    env.parse_type("struct floatfloatpair { float4 a; float4 b; };");
    assert!(env.test(model, "void func(int4,floatfloatpair);", "void,EDI,XMM0:8"));
    env.parse_type("struct doublefloatpair { float8 a; float4 b; };");
    assert!(env.test(model, "void func(int4,doublefloatpair);", "void,EDI,join XMM1:8 XMM0:8"));
    env.parse_type("struct floatfloatfloat { float4 a; float4 b; float4 c; };");
    assert!(env.test(model, "void func(floatfloatfloat,int8);", "void,join XMM1:4 XMM0:8,RDI"));
    env.parse_type("struct intintintint { int4 a; int4 b; int4 c; int4 d; };");
    assert!(env.test(model, "void func(intintintint);", "void,join RSI RDI"));
    assert!(env.test(model, "void func(int4,intintintint);", "void,EDI,join RDX RSI"));
    env.parse_type("struct intintintintint { int4 a; int4 b; int4 c; int4 d; int4 e;};");
    assert!(env.test(model, "void func(intintintintint);", "void,stack8:20"));
    assert!(env.test(
        model,
        "void func(float4,float4,float4,float4,float4,float4,float4,float4,longfloatpair);",
        "void,XMM0:4,XMM1:4,XMM2:4,XMM3:4,XMM4:4,XMM5:4,XMM6:4,XMM7:4,stack8:16"
    ));
    assert!(env.test(model, "void func(xunknown4,xunknown8);", "void,EDI,RSI"));
    assert!(env.test(model, "intintintint func(void);", "join RDX RAX"));
    assert!(env.test(model, "floatintpair func(void);", "RAX"));
    assert!(env.test(model, "longfloatpair func(void);", "join XMM0:8 RAX"));
    assert!(env.test(model, "longdoublepair func(void);", "join XMM0:8 RAX"));
    assert!(env.test(model, "doubleintpair func(void);", "join RAX XMM0:8"));
    assert!(env.test(model, "floatfloatfloat func(void);", "join XMM1:4 XMM0:8"));
    env.parse_type("struct doubledoublepair { float8 a; float8 b; };");
    assert!(env.test(model, "doubledoublepair func(void);", "join XMM1:8 XMM0:8"));
    assert!(env.test(model, "floatfloatpair func(void);", "XMM0:8"));
    assert!(env.test(model, "intintintintint func(void);", "RAX,RDI"));
    env.parse_type("struct doubleintintint { float8 a; int4 b; int4 c; int4 d; };");
    assert!(env.test(model, "doubleintintint func(void);", "RAX,RDI"));
}

#[test]
fn paramstore_ppc64be_stdcall() {
    let mut env = ParamStoreEnvironment::build_arch("PowerPC:BE:64:default:default");
    let model = env.get_model("__stdcall");
    assert!(env.test(model, "void func(int4 a,float4 b,float8 c);", "void,r3:4,join f1,f2"));
    assert!(env.test(model, "void func(float8 a,int8 b,float8 c);", "void,f1,r4,f2"));
    env.parse_type("struct sparm { int4 a; float8 dd; };");
    let proto = "void func(int4 c,float8 ff,int4 d,float16 ld,sparm s,float8 gg,sparm t,int4 e,float8 hh);";
    let res = "void,r3:4,f1,r5:4,join f2 f3,join r8 r9,f4,stack70:16,stack84:4,f5";
    assert!(env.test(model, proto, res));
}

#[test]
fn paramstore_mips32be_stdcall() {
    let mut env = ParamStoreEnvironment::build_arch("MIPS:BE:32:default:default");
    let model = env.get_model("__stdcall");
    assert!(env.test(model, "void func(int2 a,int4 b,char c);", "void,a0:2,a1,a2:1"));
    assert!(env.test(model, "void func(float8 a,float8 b);", "void,f12_13,f14_15"));
    assert!(env.test(model, "void func(float4 a,float4 b);", "void,f12,f14"));
    assert!(env.test(model, "void func(float4 a,float8 b);", "void,f12,f14_15"));
    assert!(env.test(model, "void func(float8 a,float4 b);", "void,f12_13,f14"));
    assert!(env.test(model, "void func(int4 a,int4 b,int4 c,int4 d);", "void,a0,a1,a2,a3"));
    assert!(env.test(
        model,
        "void func(float8 a,int4 b,float8 c);",
        "void,f12_13,a2,stack10:8"
    ));
    assert!(env.test(model, "void func(float8 a,int4 b,int4 c);", "void,f12_13,a2,a3"));
    assert!(env.test(model, "void func(float4 a,int4 b,int4 c);", "void,f12,a1,a2"));
    assert!(env.test(
        model,
        "void func(int4 a,int4 b,int4 c,float8 d);",
        "void,a0,a1,a2,stack10:8"
    ));
    assert!(env.test(model, "void func(int4 a,int4 b,int4 c,float4 d);", "void,a0,a1,a2,a3"));
    assert!(env.test(model, "void func(int4 a,int4 b,float8 c);", "void,a0,a1,join a2 a3"));
    assert!(env.test(model, "void func(int4 a,float8 b);", "void,a0,join a2 a3"));
    assert!(env.test(
        model,
        "void func(float4 a,float4 b,float4 c,float4 d);",
        "void,f12,f14,a2,a3"
    ));
    assert!(env.test(
        model,
        "void func(float4 a,int4 b,float4 c,int4 d);",
        "void,f12,a1,a2,a3"
    ));
    assert!(env.test(model, "void func(float8 a,float4 b,float4 c);", "void,f12_13,f14,a3"));
    assert!(env.test(
        model,
        "void func(float4 a,float4 b,float8 c);",
        "void,f12,f14,join a2 a3"
    ));
    assert!(env.test(model, "void func(int4 a,float4 b,int4 c,float4 d);", "void,a0,a1,a2,a3"));
    assert!(env.test(model, "void func(int4 a,float4 b,int4 c,int4 d);", "void,a0,a1,a2,a3"));
    assert!(env.test(model, "void func(int4 a,int4 b,float4 c,int4 d);", "void,a0,a1,a2,a3"));
    assert!(env.test(model, "int4 func(void);", "v0"));
    assert!(env.test(model, "float4 func(void);", "f0"));
    assert!(env.test(model, "float8 func(void);", "f0_1"));
    env.parse_type("struct onefieldstruct { int4 a; };");
    env.parse_type("struct twofieldstruct { int4 a; int4 b; };");
    assert!(env.test(model, "onefieldstruct func(int4 a);", "v0,a0,a1"));
    assert!(env.test(model, "twofieldstruct func(int4 a);", "v0,a0,a1"));
    assert!(env.test(model, "void func(twofieldstruct a);", "void,join a0 a1"));
    env.parse_type("struct intdouble { int4 a; float8 b; };");
    assert!(env.test(model, "void func(intdouble a);", "void,join a0 a1 a2 a3"));
}

#[test]
fn paramstore_aarch64_cdecl() {
    let mut env = ParamStoreEnvironment::build_arch("AARCH64:LE:64:v8A:default");
    let model = env.get_model("__cdecl");
    assert!(env.test(model, "void func(int2 a,int4 b,int1 c);", "void,w0:2,w1,w2:1"));
    assert!(env.test(model, "void func(int4, int4);", "void,w0,w1"));
    assert!(env.test(model, "void func(int8,int8);", "void,x0,x1"));
    assert!(env.test(model, "void func(float4,float4);", "void,s0,s1"));
    assert!(env.test(model, "void func(float8,float8);", "void,d0,d1"));
    assert!(env.test(model, "void func(int4,float4,int4,float4);", "void,w0,s0,w1,s1"));
    assert!(env.test(model, "void func(float4,int4,float4,int4);", "void,s0,w0,s1,w1"));
    assert!(env.test(model, "void func(int4,float8,float8,int4);", "void,w0,d0,d1,w1"));
    assert!(env.test(model, "void func(float8,int8,int8,float8);", "void,d0,x0,x1,d1"));
    assert!(env.test(model, "void func(float16);", "void,q0"));
    assert!(env.test(model, "void func(float4,float16);", "void,s0,q1"));
    assert!(env.test(
        model,
        "void func(int4,int4,int4,int4,int4,int4,int4,int4,int4,int4);",
        "void,w0,w1,w2,w3,w4,w5,w6,w7,stack0:4,stack8:4"
    ));
    assert!(env.test(
        model,
        "void func(float4,float4,float4,float4,float4,float4,float4,float4,float4,float4);",
        "void,s0,s1,s2,s3,s4,s5,s6,s7,stack0:4,stack8:4"
    ));
    assert!(env.test(
        model,
        "void func(float4,float4,float4,float4,float4,float4,float4,float4,float16);",
        "void,s0,s1,s2,s3,s4,s5,s6,s7,stack0:16"
    ));
    assert!(env.test(
        model,
        "void func(float4,float4,float4,float4,float4,float4,float4,float4,float4,float16);",
        "void,s0,s1,s2,s3,s4,s5,s6,s7,stack0:4,stack10:16"
    ));
    assert!(env.test(
        model,
        "void func(int4,int4,int4,int4,int4,int4,int4,int4,int4,float4);",
        "void,w0,w1,w2,w3,w4,w5,w6,w7,stack0:4,s0"
    ));
    assert!(env.test(
        model,
        "void func(float4,float4,float4,float4,float4,float4,float4,float4,float4,int4);",
        "void,s0,s1,s2,s3,s4,s5,s6,s7,stack0:4,w0"
    ));
    env.parse_type("struct intpair { int4 a; int4 b;};");
    assert!(env.test(model, "void func(intpair);", "void,x0"));
    env.parse_type("struct longpair { int8 a; int8 b; };");
    assert!(env.test(model, "void func(longpair);", "void,join x1 x0"));
    env.parse_type("struct longquad { int8 a; int8 b; int8 c; int8 d; };");
    assert!(env.test(model, "void func(longquad);", "void,x0"));
    env.parse_type("struct floatdouble { float4 a; float8 b; };");
    assert!(env.test(model, "void func(floatdouble);", "void,join x1 x0"));
    env.parse_type("struct intfloat { int4 a; float4 b; };");
    assert!(env.test(model, "void func(intfloat);", "void,x0"));
    env.parse_type("struct longdoublestruct { int8 a; float8 b; };");
    assert!(env.test(model, "void func(longdoublestruct);", "void,join x1 x0"));
    assert!(env.test(model, "int4 func(void);", "w0"));
    assert!(env.test(model, "float4 func(void);", "s0"));
    assert!(env.test(model, "float8 func(void);", "d0"));
    assert!(env.test(model, "intpair func(void);", "x0"));
    assert!(env.test(model, "longpair func(void);", "join x1 x0"));
    assert!(env.test(model, "longquad func(void);", "void,x8"));
    env.parse_type("struct floatpair { float4 a; float4 b; };");
    assert!(env.test(model, "void func(floatpair);", "void,join s1 s0"));
    env.parse_type("struct floatpairpair { floatpair a; floatpair b; };");
    assert!(env.test(model, "void func(floatpairpair);", "void,join s3 s2 s1 s0"));
    env.parse_type("struct doublequad { float8 a; float8 b; float8 c; float8 d; };");
    assert!(env.test(model, "void func(doublequad);", "void,join d3 d2 d1 d0"));
}
