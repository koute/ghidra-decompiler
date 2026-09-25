#![cfg(feature = "toy")]

use std::io::Cursor;

use ghidra_decompiler::address::Address;
use ghidra_decompiler::architecture::{Architecture, ArchitectureCapability, ErrorStream};
use ghidra_decompiler::fspec::{ModelId, ParamActive, ParamTrial, ParameterPieces, PrototypePieces};
use ghidra_decompiler::grammar::parse_protopieces;
use ghidra_decompiler::space::SpaceRef;
use ghidra_decompiler::types::{TypeId, TypeMetatype};
use ghidra_decompiler::xml::DocumentStorage;
use ghidra_decompiler::xml_arch::XML_ARCHITECTURE_CAPABILITY;

const MODEL1: &str = concat!(
    "<prototype name=\"__model1\" extrapop=\"unknown\" stackshift=\"4\">",
    "<input pointermax=\"4\">",
    "<pentry minsize=\"1\" maxsize=\"4\">",
    "<register name=\"r12\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\">",
    "<register name=\"r11\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\">",
    "<register name=\"r10\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\">",
    "<register name=\"r9\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\">",
    "<register name=\"r8\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"500\" align=\"4\">",
    "<addr offset=\"0\" space=\"stack\"/>",
    "</pentry>",
    "</input>",
    "<output>",
    "<pentry minsize=\"1\" maxsize=\"4\">",
    "<register name=\"r12\"/>",
    "</pentry>",
    "</output>",
    "</prototype>"
);

const MODEL2: &str = concat!(
    "<prototype name=\"__model2\" extrapop=\"unknown\" stackshift=\"4\">",
    "<input>",
    "<pentry minsize=\"1\" maxsize=\"4\" metatype=\"ptr\"><register name=\"r1\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\" metatype=\"ptr\"><register name=\"r2\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\" metatype=\"float\" extension=\"float\"><register name=\"r3\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\" metatype=\"float\" extension=\"float\"><register name=\"r4\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\" metatype=\"float\" extension=\"float\"><register name=\"r5\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\">",
    "<register name=\"r10\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\">",
    "<register name=\"r9\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\">",
    "<register name=\"r8\"/>",
    "</pentry>",
    "<pentry minsize=\"5\" maxsize=\"8\">",
    "<addr space=\"join\" piece1=\"r10\" piece2=\"r9\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"500\" align=\"4\">",
    "<addr offset=\"0\" space=\"stack\"/>",
    "</pentry>",
    "</input>",
    "<output>",
    "<pentry minsize=\"1\" maxsize=\"4\">",
    "<register name=\"r12\"/>",
    "</pentry>",
    "</output>",
    "</prototype>"
);

const MODEL3: &str = concat!(
    "<prototype name=\"__model3\" extrapop=\"unknown\" stackshift=\"4\">",
    "<input>",
    "<group>",
    "<pentry minsize=\"1\" maxsize=\"4\" metatype=\"float\" extension=\"float\"><register name=\"r3\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\"> ",
    "<register name=\"r10\"/> ",
    "</pentry> ",
    "</group> ",
    "<group>",
    "<pentry minsize=\"1\" maxsize=\"4\" metatype=\"float\" extension=\"float\"><register name=\"r4\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\"> ",
    "<register name=\"r9\"/> ",
    "</pentry> ",
    "</group>",
    "<group>",
    "<pentry minsize=\"1\" maxsize=\"4\" metatype=\"float\" extension=\"float\"><register name=\"r5\"/>",
    "</pentry>",
    "<pentry minsize=\"1\" maxsize=\"4\"> ",
    "<register name=\"r8\"/> ",
    "</pentry> ",
    "</group> ",
    "<pentry minsize=\"1\" maxsize=\"500\" align=\"4\"> ",
    "<addr offset=\"0\" space=\"stack\"/> ",
    "</pentry> ",
    "</input>",
    "<output>",
    "<pentry minsize=\"1\" maxsize=\"4\">",
    "<register name=\"r12\"/>",
    "</pentry>",
    "</output>",
    "</prototype>"
);

struct FuncProtoTestEnvironment {
    glb: Box<Architecture>,
}

impl FuncProtoTestEnvironment {
    fn build() -> FuncProtoTestEnvironment {
        let mut store = DocumentStorage::new();
        let doc = store
            .parse_document(b"<binaryimage arch=\"Toy:LE:32:default:default\"></binaryimage>")
            .expect("invalid binaryimage document");
        store.register_tag(doc.get_root());
        let mut extensions = String::from("<specextensions> ");
        for model in [MODEL1, MODEL2, MODEL3] {
            extensions.push_str(model);
            extensions.push('\n');
        }
        extensions.push_str("</specextensions>\n");
        let doc = store
            .parse_document(extensions.as_bytes())
            .expect("invalid specextensions document");
        store.register_tag(doc.get_root());
        let estream: ErrorStream = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
        let mut glb = XML_ARCHITECTURE_CAPABILITY
            .build_architecture("", "", Some(estream))
            .expect("xml architecture construction failed");
        glb.init(&mut store).expect("Architecture did not load");
        FuncProtoTestEnvironment { glb }
    }

    fn get_model(&self, nm: &str) -> ModelId {
        *self.glb.proto_model_map.get(nm).expect("missing prototype model")
    }

    fn assign(&mut self, model: ModelId, text: &str) -> Vec<ParameterPieces> {
        let mut stream = Cursor::new(text.as_bytes().to_vec());
        let mut pieces = PrototypePieces::default();
        parse_protopieces(&mut pieces, &mut stream, &mut self.glb).expect("prototype parse failed");
        let mut res = Vec::new();
        let glb = &mut *self.glb;
        ghidra_decompiler::fspec::assign_storage_glb(model, &pieces, &mut res, false, glb)
            .expect("parameter storage assignment failed");
        res
    }

    fn derive(&self, model: ModelId, active: &mut ParamActive) {
        self.glb
            .proto_models
            .get(model)
            .derive_input_map(active, &self.glb.manager)
            .expect("input map derivation failed");
    }

    fn register_address(&self, nm: &str) -> (Address, u32) {
        let data = self
            .glb
            .translate
            .as_ref()
            .expect("missing translator")
            .get_register(nm)
            .expect("unknown register");
        (data.get_addr(), data.size)
    }

    fn register_equal(&self, piece: &ParameterPieces, nm: &str) -> bool {
        let (addr, _size) = self.register_address(nm);
        same_space(addr.get_space(), piece.addr.get_space()) && addr.get_offset() == piece.addr.get_offset()
    }

    fn stack_space(&self) -> SpaceRef {
        self.glb.manager.get_stack_space().expect("missing stack space")
    }

    fn is_stack(&self, piece: &ParameterPieces) -> bool {
        same_space(Some(&self.stack_space()), piece.addr.get_space())
    }

    fn is_join(&self, piece: &ParameterPieces) -> bool {
        let join = self.glb.manager.get_join_space().expect("missing join space");
        same_space(Some(&join), piece.addr.get_space())
    }

    fn type_name(&self, piece: &ParameterPieces) -> String {
        let types = self.glb.types.as_ref().expect("missing type factory");
        types
            .get(piece.tp.expect("missing parameter type"))
            .get_name()
            .to_string()
    }

    fn metatype(&self, piece: &ParameterPieces) -> TypeMetatype {
        let types = self.glb.types.as_ref().expect("missing type factory");
        types.get(piece.tp.expect("missing parameter type")).get_metatype()
    }

    fn pointed_name(&self, piece: &ParameterPieces) -> String {
        let types = self.glb.types.as_ref().expect("missing type factory");
        let ptr_to: TypeId = types.get(piece.tp.expect("missing parameter type")).get_ptr_to();
        types.get(ptr_to).get_name().to_string()
    }

    fn register_active(&self, param_active: &mut ParamActive, nm: &str, sz: i32) {
        let (addr, _size) = self.register_address(nm);
        param_active.register_trial(&addr, sz);
        let num = param_active.get_num_trials();
        param_active.get_trial_mut(num - 1).mark_active();
    }

    fn stack_active(&self, param_active: &mut ParamActive, off: u64, sz: i32) {
        param_active.register_trial(&Address::new(self.stack_space(), off), sz);
        let num = param_active.get_num_trials();
        param_active.get_trial_mut(num - 1).mark_active();
    }

    fn register_used(&self, trial: &ParamTrial, nm: &str) -> bool {
        if !trial.is_used() {
            return false;
        }
        let (addr, size) = self.register_address(nm);
        *trial.get_address() == addr && trial.get_size() == size as i32
    }

    fn stack_used(&self, trial: &ParamTrial, off: u64, sz: i32) -> bool {
        if !trial.is_used() {
            return false;
        }
        let addr = Address::new(self.stack_space(), off);
        *trial.get_address() == addr && trial.get_size() == sz
    }
}

fn same_space(first: Option<&SpaceRef>, second: Option<&SpaceRef>) -> bool {
    match (first, second) {
        (Some(one), Some(two)) => one.get_index() == two.get_index(),
        (None, None) => true,
        _ => false,
    }
}

#[test]
fn funcproto_register() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model1");
    let res = env.assign(model, "void func(int4 a,int4 b);");
    assert_eq!(res.len(), 3);
    assert!(res[0].addr.is_invalid());
    assert!(env.register_equal(&res[1], "r12"));
    assert!(env.register_equal(&res[2], "r11"));
}

#[test]
fn funcproto_smallregister() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model1");
    let res = env.assign(model, "int4 func(char a,int4 b,int2 c,int4 d);");
    assert_eq!(res.len(), 5);
    assert!(env.register_equal(&res[0], "r12"));
    assert_eq!(env.type_name(&res[0]), "int4");
    assert!(env.register_equal(&res[1], "r12"));
    assert_eq!(env.type_name(&res[1]), "char");
    assert!(env.register_equal(&res[2], "r11"));
    assert_eq!(env.type_name(&res[2]), "int4");
    assert!(env.register_equal(&res[3], "r10"));
    assert_eq!(env.type_name(&res[3]), "int2");
    assert!(env.register_equal(&res[4], "r9"));
    assert_eq!(env.type_name(&res[4]), "int4");
}

#[test]
fn funcproto_stackalign() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model1");
    let res = env.assign(model, "int4 func(int4 a,int4 b,int4 c,int4 d,int4 e,int2 f,int1 *g);");
    assert_eq!(res.len(), 8);
    assert!(env.register_equal(&res[0], "r12"));
    assert_eq!(env.type_name(&res[0]), "int4");
    assert!(env.register_equal(&res[1], "r12"));
    assert_eq!(res[1].tp, res[0].tp);
    assert!(env.register_equal(&res[2], "r11"));
    assert_eq!(res[2].tp, res[0].tp);
    assert!(env.register_equal(&res[3], "r10"));
    assert_eq!(res[3].tp, res[0].tp);
    assert!(env.register_equal(&res[4], "r9"));
    assert_eq!(res[4].tp, res[0].tp);
    assert!(env.register_equal(&res[5], "r8"));
    assert_eq!(res[5].tp, res[0].tp);
    assert!(env.is_stack(&res[6]));
    assert_eq!(res[6].addr.get_offset(), 0x0);
    assert_eq!(env.type_name(&res[6]), "int2");
    assert!(env.is_stack(&res[7]));
    assert_eq!(res[7].addr.get_offset(), 0x4);
    assert_eq!(env.metatype(&res[7]), TypeMetatype::Ptr);
}

#[test]
fn funcproto_pointeroverflow() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model1");
    let res = env.assign(model, "int2 func(int4 a,int8 b,int4 c);");
    assert_eq!(res.len(), 4);
    assert!(env.register_equal(&res[0], "r12"));
    assert_eq!(env.type_name(&res[0]), "int2");
    assert!(env.register_equal(&res[1], "r12"));
    assert_eq!(env.type_name(&res[1]), "int4");
    assert!(env.register_equal(&res[2], "r11"));
    assert_eq!(env.metatype(&res[2]), TypeMetatype::Ptr);
    assert_eq!(env.pointed_name(&res[2]), "int8");
    assert_eq!(res[2].flags, ParameterPieces::INDIRECTSTORAGE);
    assert!(env.register_equal(&res[3], "r10"));
    assert_eq!(env.type_name(&res[3]), "int4");
}

#[test]
fn funcproto_stackoverflow() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model2");
    let res = env.assign(model, "char func(int4 a,int8 b,int4 c);");
    assert_eq!(res.len(), 4);
    assert!(env.register_equal(&res[0], "r12"));
    assert_eq!(env.type_name(&res[0]), "char");
    assert!(env.register_equal(&res[1], "r10"));
    assert_eq!(env.type_name(&res[1]), "int4");
    assert!(env.is_stack(&res[2]));
    assert_eq!(res[2].addr.get_offset(), 0x0);
    assert_eq!(env.type_name(&res[2]), "int8");
    assert!(env.register_equal(&res[3], "r9"));
    assert_eq!(env.type_name(&res[3]), "int4");
}

#[test]
fn funcproto_floatreg() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model2");
    let res = env.assign(model, "void func(int4 a,float4 b,float4 c,int4 d,float4 d);");
    assert_eq!(res.len(), 6);
    assert!(res[0].addr.is_invalid());
    assert!(env.register_equal(&res[1], "r10"));
    assert!(env.register_equal(&res[2], "r3"));
    assert_eq!(env.type_name(&res[2]), "float4");
    assert!(env.register_equal(&res[3], "r4"));
    assert_eq!(env.type_name(&res[3]), "float4");
    assert!(env.register_equal(&res[4], "r9"));
    assert!(env.register_equal(&res[5], "r5"));
    assert_eq!(env.type_name(&res[5]), "float4");
}

#[test]
fn funcproto_floattogeneric() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model2");
    let res = env.assign(
        model,
        "float4 func(int4 a,float4 b,float4 c,float4 d,float4 e,float4 f);",
    );
    assert_eq!(res.len(), 7);
    assert!(env.register_equal(&res[0], "r12"));
    assert_eq!(env.type_name(&res[0]), "float4");
    assert!(env.register_equal(&res[1], "r10"));
    assert!(env.register_equal(&res[2], "r3"));
    assert_eq!(env.type_name(&res[2]), "float4");
    assert!(env.register_equal(&res[3], "r4"));
    assert_eq!(env.type_name(&res[3]), "float4");
    assert!(env.register_equal(&res[4], "r5"));
    assert_eq!(env.type_name(&res[4]), "float4");
    assert!(env.register_equal(&res[5], "r9"));
    assert_eq!(env.type_name(&res[5]), "float4");
    assert!(env.register_equal(&res[6], "r8"));
    assert_eq!(env.type_name(&res[6]), "float4");
}

#[test]
fn funcproto_grouped() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model3");
    let res = env.assign(model, "float4 func(int4 a,float4 b,float4 c,int4 d,float4 e);");
    assert_eq!(res.len(), 6);
    assert!(env.register_equal(&res[0], "r12"));
    assert_eq!(env.type_name(&res[0]), "float4");
    assert!(env.register_equal(&res[1], "r10"));
    assert_eq!(env.type_name(&res[1]), "int4");
    assert!(env.register_equal(&res[2], "r4"));
    assert_eq!(env.type_name(&res[2]), "float4");
    assert!(env.register_equal(&res[3], "r5"));
    assert_eq!(env.type_name(&res[3]), "float4");
    assert!(env.is_stack(&res[4]));
    assert_eq!(res[4].addr.get_offset(), 0x0);
    assert_eq!(env.type_name(&res[4]), "int4");
    assert!(env.is_stack(&res[5]));
    assert_eq!(res[5].addr.get_offset(), 0x4);
    assert_eq!(env.type_name(&res[5]), "float4");
}

#[test]
fn funcproto_join() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model2");
    let res = env.assign(model, "int2 func(int8 a,int4 b,int4 c);");
    assert_eq!(res.len(), 4);
    assert!(env.register_equal(&res[0], "r12"));
    assert_eq!(env.type_name(&res[0]), "int2");
    assert!(env.is_join(&res[1]));
    assert_eq!(env.type_name(&res[1]), "int8");
    assert!(env.register_equal(&res[2], "r8"));
    assert_eq!(env.type_name(&res[2]), "int4");
    assert!(env.is_stack(&res[3]));
    assert_eq!(res[3].addr.get_offset(), 0);
    assert_eq!(env.type_name(&res[3]), "int4");
}

#[test]
fn funcproto_nojoin() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model2");
    let res = env.assign(model, "int4 func(int4 a,int8 b,int4 c);");
    assert_eq!(res.len(), 4);
    assert!(env.register_equal(&res[0], "r12"));
    assert_eq!(env.type_name(&res[0]), "int4");
    assert!(env.register_equal(&res[1], "r10"));
    assert_eq!(env.type_name(&res[1]), "int4");
    assert!(env.is_stack(&res[2]));
    assert_eq!(res[2].addr.get_offset(), 0);
    assert_eq!(env.type_name(&res[2]), "int8");
    assert!(env.register_equal(&res[3], "r9"));
    assert_eq!(env.type_name(&res[3]), "int4");
}

#[test]
fn funcproto_hiddenreturn() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model1");
    let res = env.assign(model, "int8 func(int4 a,int4 b);");
    assert_eq!(res.len(), 4);
    assert!(env.register_equal(&res[0], "r12"));
    assert_eq!(env.metatype(&res[0]), TypeMetatype::Ptr);
    assert_eq!(env.pointed_name(&res[0]), "int8");
    assert!(env.register_equal(&res[1], "r12"));
    assert_eq!(res[1].flags, ParameterPieces::HIDDENRETPARM);
    assert_eq!(env.metatype(&res[1]), TypeMetatype::Ptr);
    assert_eq!(env.pointed_name(&res[1]), "int8");
    assert!(env.register_equal(&res[2], "r11"));
    assert_eq!(env.type_name(&res[2]), "int4");
    assert!(env.register_equal(&res[3], "r10"));
    assert_eq!(env.type_name(&res[3]), "int4");
}

#[test]
fn funcproto_mixedmeta() {
    let mut env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model2");
    let res = env.assign(model, "int4 func(char *a,int4 b,float4 c,int4 *d);");
    assert_eq!(res.len(), 5);
    assert!(env.register_equal(&res[0], "r12"));
    assert!(env.register_equal(&res[1], "r1"));
    assert_eq!(env.metatype(&res[1]), TypeMetatype::Ptr);
    assert!(env.register_equal(&res[2], "r10"));
    assert!(env.register_equal(&res[3], "r3"));
    assert!(env.register_equal(&res[4], "r2"));
    assert_eq!(env.metatype(&res[4]), TypeMetatype::Ptr);
}

#[test]
fn funcproto_recoverbasic() {
    let env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model1");
    let mut param_active = ParamActive::new(false);
    env.register_active(&mut param_active, "r11", 4);
    env.register_active(&mut param_active, "r10", 4);
    env.register_active(&mut param_active, "r12", 4);
    env.derive(model, &mut param_active);
    assert_eq!(param_active.get_num_trials(), 3);
    assert!(env.register_used(param_active.get_trial(0), "r12"));
    assert!(env.register_used(param_active.get_trial(1), "r11"));
    assert!(env.register_used(param_active.get_trial(2), "r10"));
}

#[test]
fn funcproto_recoversmallreg() {
    let env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model1");
    let mut param_active = ParamActive::new(false);
    env.register_active(&mut param_active, "r11", 4);
    env.register_active(&mut param_active, "r12l", 2);
    env.register_active(&mut param_active, "r10l", 2);
    env.derive(model, &mut param_active);
    assert_eq!(param_active.get_num_trials(), 3);
    assert!(env.register_used(param_active.get_trial(0), "r12l"));
    assert!(env.register_used(param_active.get_trial(1), "r11"));
    assert!(env.register_used(param_active.get_trial(2), "r10l"));
}

#[test]
fn funcproto_recoverstack() {
    let env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model2");
    let mut param_active = ParamActive::new(false);
    env.register_active(&mut param_active, "r10", 4);
    env.stack_active(&mut param_active, 0, 2);
    env.register_active(&mut param_active, "r8", 4);
    env.stack_active(&mut param_active, 4, 4);
    env.register_active(&mut param_active, "r9", 4);
    env.derive(model, &mut param_active);
    assert_eq!(param_active.get_num_trials(), 10);
    for slot in 0..5 {
        assert!(param_active.get_trial(slot).is_unref());
    }
    for slot in 0..5 {
        assert!(!param_active.get_trial(slot).is_used());
    }
    assert!(env.register_used(param_active.get_trial(5), "r10"));
    assert!(env.register_used(param_active.get_trial(6), "r9"));
    assert!(env.register_used(param_active.get_trial(7), "r8"));
    assert!(env.stack_used(param_active.get_trial(8), 0, 2));
    assert!(env.stack_used(param_active.get_trial(9), 4, 4));
}

#[test]
fn funcproto_recoverunrefregister() {
    let env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model1");
    let mut param_active = ParamActive::new(false);
    env.register_active(&mut param_active, "r12", 4);
    env.register_active(&mut param_active, "r10", 4);
    env.derive(model, &mut param_active);
    assert_eq!(param_active.get_num_trials(), 3);
    assert!(env.register_used(param_active.get_trial(0), "r12"));
    assert!(env.register_used(param_active.get_trial(1), "r11"));
    assert!(param_active.get_trial(1).is_unref());
    assert!(env.register_used(param_active.get_trial(2), "r10"));
}

#[test]
fn funcproto_recoverunrefstack() {
    let env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model2");
    let mut param_active = ParamActive::new(false);
    env.stack_active(&mut param_active, 4, 4);
    env.stack_active(&mut param_active, 12, 4);
    env.register_active(&mut param_active, "r8", 4);
    env.register_active(&mut param_active, "r9", 4);
    env.register_active(&mut param_active, "r10", 4);
    env.derive(model, &mut param_active);
    assert_eq!(param_active.get_num_trials(), 12);
    for slot in 0..5 {
        assert!(param_active.get_trial(slot).is_unref());
    }
    for slot in 0..5 {
        assert!(!param_active.get_trial(slot).is_used());
    }
    assert!(env.register_used(param_active.get_trial(5), "r10"));
    assert!(env.register_used(param_active.get_trial(6), "r9"));
    assert!(env.register_used(param_active.get_trial(7), "r8"));
    assert!(env.stack_used(param_active.get_trial(8), 0, 4));
    assert!(param_active.get_trial(8).is_unref());
    assert!(env.stack_used(param_active.get_trial(9), 4, 4));
    assert!(env.stack_used(param_active.get_trial(10), 8, 4));
    assert!(param_active.get_trial(10).is_unref());
    assert!(env.stack_used(param_active.get_trial(11), 12, 4));
}

#[test]
fn funcproto_recovergroups() {
    let env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model3");
    let mut param_active = ParamActive::new(false);
    env.register_active(&mut param_active, "r3", 4);
    env.register_active(&mut param_active, "r5", 4);
    env.register_active(&mut param_active, "r9", 4);
    env.derive(model, &mut param_active);
    assert_eq!(param_active.get_num_trials(), 3);
    assert!(env.register_used(param_active.get_trial(0), "r3"));
    assert!(env.register_used(param_active.get_trial(1), "r9"));
    assert!(env.register_used(param_active.get_trial(2), "r5"));
}

#[test]
fn funcproto_recoverholes() {
    let env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model1");
    let mut param_active = ParamActive::new(false);
    env.register_active(&mut param_active, "r8", 4);
    env.register_active(&mut param_active, "r12", 4);
    env.stack_active(&mut param_active, 0, 4);
    env.derive(model, &mut param_active);
    assert_eq!(param_active.get_num_trials(), 6);
    assert!(env.register_used(param_active.get_trial(0), "r12"));
    assert!(!param_active.get_trial(1).is_used());
    assert!(param_active.get_trial(1).is_unref());
    assert!(!param_active.get_trial(2).is_used());
    assert!(param_active.get_trial(2).is_unref());
    assert!(!param_active.get_trial(3).is_used());
    assert!(param_active.get_trial(3).is_unref());
    assert!(!param_active.get_trial(4).is_used());
    assert!(!param_active.get_trial(5).is_used());
}

#[test]
fn funcproto_recoverfloat() {
    let env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model2");
    let mut param_active = ParamActive::new(false);
    env.register_active(&mut param_active, "r10", 4);
    env.register_active(&mut param_active, "r5", 4);
    env.register_active(&mut param_active, "r3", 4);
    env.derive(model, &mut param_active);
    assert_eq!(param_active.get_num_trials(), 6);
    assert!(param_active.get_trial(0).is_unref());
    assert!(param_active.get_trial(1).is_unref());
    assert!(!param_active.get_trial(0).is_used());
    assert!(!param_active.get_trial(1).is_used());
    assert!(env.register_used(param_active.get_trial(2), "r3"));
    assert!(env.register_used(param_active.get_trial(3), "r4"));
    assert!(env.register_used(param_active.get_trial(4), "r5"));
    assert!(env.register_used(param_active.get_trial(5), "r10"));
}

#[test]
fn funcproto_recovermixedmeta() {
    let env = FuncProtoTestEnvironment::build();
    let model = env.get_model("__model2");
    let mut param_active = ParamActive::new(false);
    env.register_active(&mut param_active, "r10", 4);
    env.register_active(&mut param_active, "r4", 4);
    env.register_active(&mut param_active, "r1", 4);
    env.derive(model, &mut param_active);
    assert_eq!(param_active.get_num_trials(), 6);
    assert!(env.register_used(param_active.get_trial(0), "r1"));
    assert!(param_active.get_trial(1).is_unref());
    assert!(!param_active.get_trial(1).is_used());
    assert!(env.register_used(param_active.get_trial(2), "r3"));
    assert!(env.register_used(param_active.get_trial(3), "r4"));
    assert!(param_active.get_trial(4).is_unref());
    assert!(!param_active.get_trial(4).is_used());
    assert!(env.register_used(param_active.get_trial(5), "r10"));
}
