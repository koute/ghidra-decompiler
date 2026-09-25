use std::collections::BTreeSet;
use std::path::PathBuf;
use std::sync::Arc;

use ghidra_decompiler::address::Address;
use ghidra_decompiler::error::Error;
use ghidra_decompiler::loadimage::{LoadImage, RawLoadImage, SharedLoadImage};
use ghidra_decompiler::opcodes::{OpCode, get_opname};
use ghidra_decompiler::pcoderaw::VarnodeData;
use ghidra_decompiler::sleigh_arch::{
    LanguageRegistry, normalize_architecture, normalize_endian, normalize_processor, normalize_size,
};
use ghidra_decompiler::translate::{AssemblyEmit, PcodeEmit, Translate};

fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

#[test]
fn normalization_matches_sleigh_arch() {
    assert_eq!(normalize_processor("i386"), "x86");
    assert_eq!(normalize_processor("ARM"), "ARM");
    assert_eq!(normalize_endian("big"), "BE");
    assert_eq!(normalize_endian("little"), "LE");
    assert_eq!(normalize_endian("LE"), "LE");
    assert_eq!(normalize_size("32bit"), "32");
    assert_eq!(normalize_size("64-bit"), "64");
    assert_eq!(
        normalize_architecture("x86:LE:64:default").expect("valid id"),
        "x86:LE:64:default:default"
    );
    assert_eq!(
        normalize_architecture("i386:little:32-bit:default:gcc").expect("valid id"),
        "x86:LE:32:default:gcc"
    );
    assert_eq!(
        normalize_architecture("x86:LE:32:System Management Mode:default").expect("valid id"),
        "x86:LE:32:System Management Mode:default"
    );
    match normalize_architecture("x86:LE") {
        Err(Error::Lowlevel(message)) => {
            assert_eq!(message, "Architecture string does not look like sleigh id: x86:LE")
        }
        other => panic!("unexpected result {other:?}"),
    }
}

fn manifest_languages() -> BTreeSet<String> {
    let text = std::fs::read_to_string(crate_dir().join("tests/data/sleigh/manifest.tsv")).expect("missing manifest");
    text.lines()
        .skip(1)
        .filter(|line| !line.is_empty())
        .map(|line| line.split('\t').nth(1).expect("language column").to_string())
        .collect()
}

#[test]
fn embedded_registry_languages() {
    let registry = LanguageRegistry::embedded();
    assert!(registry.get_warnings().is_empty());
    let manifest = manifest_languages();
    let ids: BTreeSet<String> = registry
        .get_descriptions()
        .iter()
        .map(|description| description.get_id().to_string())
        .collect();
    assert_eq!(ids.len(), registry.get_descriptions().len());
    for id in ids.iter() {
        assert!(manifest.contains(id), "language {id} missing from corpus manifest");
    }
    if cfg!(feature = "all-processors") {
        assert_eq!(ids, manifest);
    }
    for description in registry.get_descriptions() {
        assert!(
            registry.find_file(description.get_sla_file()).is_some(),
            "missing sla for {}",
            description.get_id()
        );
        assert!(registry.find_file(description.get_processor_spec()).is_some());
        for compiler in description.get_compilers() {
            assert!(registry.find_file(compiler.get_spec()).is_some());
        }
    }
    match registry.resolve_architecture("NoSuch:LE:32:default") {
        Err(Error::Lowlevel(message)) => {
            assert_eq!(message, "No sleigh specification for NoSuch:LE:32:default")
        }
        other => panic!("unexpected result {other:?}"),
    }
}

#[test]
fn compiler_selection() {
    let registry = LanguageRegistry::embedded();
    let Ok((index, archid, _)) = registry.resolve_architecture("x86:LE:64:default:gcc") else {
        return;
    };
    assert_eq!(archid, "x86:LE:64:default:gcc");
    let description = &registry.get_descriptions()[index];
    assert_eq!(description.get_compiler("gcc").expect("compiler").get_id(), "gcc");
    assert_eq!(
        description.get_compiler("nosuch").expect("compiler").get_id(),
        description
            .get_compilers()
            .iter()
            .find(|tag| tag.get_id() == "default")
            .map(|tag| tag.get_id())
            .unwrap_or_else(|| description.get_compilers()[0].get_id())
    );
}

struct Collector {
    lines: Vec<String>,
}

impl AssemblyEmit for Collector {
    fn dump(&mut self, addr: &Address, mnem: &str, body: &str) {
        self.lines.push(format!("{:x} {mnem} {body}", addr.get_offset()));
    }
}

impl PcodeEmit for Collector {
    fn dump(
        &mut self,
        _addr: &Address,
        opc: OpCode,
        outvar: Option<&VarnodeData>,
        vars: &[VarnodeData],
    ) -> ghidra_decompiler::error::Result<()> {
        let mut line = String::new();
        if let Some(out) = outvar {
            line.push_str(&format!("{:x}:{} = ", out.offset, out.size));
        }
        line.push_str(get_opname(opc));
        for var in vars {
            line.push_str(&format!(" {:x}:{}", var.offset, var.size));
        }
        self.lines.push(line);
        Ok(())
    }
}

fn decode_all(registry: &LanguageRegistry, target: &str, loader: SharedLoadImage, base: u64, size: u64) -> Vec<String> {
    let decoder = registry.build_decoder(target, loader).expect("decoder");
    let translate: &dyn Translate = &decoder.sleigh;
    let space = translate.manager().get_default_code_space().expect("code space");
    let mut collector = Collector { lines: Vec::new() };
    let mut offset = base;
    while offset < base + size {
        let addr = Address::new(space.clone(), offset);
        match translate.print_assembly(&mut collector, &addr) {
            Ok(length) => {
                if let Err(err) = translate.one_instruction(&mut collector, &addr) {
                    collector.lines.push(err.explain().to_string());
                }
                offset += length as u64;
            }
            Err(err) => {
                collector.lines.push(err.explain().to_string());
                offset += 1;
            }
        }
    }
    collector.lines
}

#[test]
fn directory_registry_matches_embedded() {
    let embedded = LanguageRegistry::embedded();
    if embedded.resolve_architecture("x86:LE:64:default").is_err() {
        return;
    }
    let directory = LanguageRegistry::from_directory(&crate_dir().join("languages/x86")).expect("directory");
    assert!(directory.resolve_architecture("x86:LE:64:default").is_ok());
    assert!(directory.resolve_architecture("ARM:LE:32:v7").is_err());
    let input = crate_dir().join("tests/data/sleigh/input/x86_LE_64_default.random.bin");
    let bytes = std::fs::read(&input).expect("corpus input");
    let size = bytes.len() as u64;
    let make_loader = || -> SharedLoadImage {
        let mut image = RawLoadImage::from_bytes("x86", bytes.clone());
        image.adjust_vma(0x1000);
        Arc::new(image)
    };
    let first = decode_all(&embedded, "x86:LE:64:default:gcc", make_loader(), 0x1000, size);
    let second = decode_all(&directory, "x86:LE:64:default:gcc", make_loader(), 0x1000, size);
    assert!(first.len() > 1000);
    assert_eq!(first, second);
}

#[test]
fn raw_load_image_fill() {
    let mut image = RawLoadImage::from_bytes("raw", vec![1, 2, 3, 4]);
    image.adjust_vma(0x100);
    let registry = LanguageRegistry::embedded();
    let Ok(decoder) = registry.build_decoder(
        "x86:LE:32:default",
        Arc::new(RawLoadImage::from_bytes("raw", Vec::new())),
    ) else {
        return;
    };
    let space = decoder.sleigh.manager().get_default_code_space().expect("code space");
    let mut buffer = [0xffu8; 6];
    image
        .load_fill(&mut buffer, &Address::new(space.clone(), 0x102))
        .expect("partial fill");
    assert_eq!(buffer, [3, 4, 0, 0, 0, 0]);
    let mut buffer = [0xffu8; 2];
    match image.load_fill(&mut buffer, &Address::new(space, 0x200)) {
        Err(Error::DataUnavail(message)) => {
            assert_eq!(message, "Unable to load 2 bytes at r0x00000200")
        }
        other => panic!("unexpected result {other:?}"),
    }
}
