use std::path::PathBuf;
use std::sync::Arc;

use ghidra_decompiler::address::{Address, RangeList};
use ghidra_decompiler::architecture::ArchitectureCapability;
use ghidra_decompiler::error::Error;
use ghidra_decompiler::loadimage::{LoadImage, LoadImageFunc, LoadImageSection};
use ghidra_decompiler::object_arch::{OBJECT_ARCHITECTURE_CAPABILITY, ObjectLoadImage, language_from_arch_type};
use ghidra_decompiler::sleigh_arch::AdjustableLoadImage;
use ghidra_decompiler::space::{AddrSpace, SpaceRef};

fn binary(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/decomp/bin")
        .join(name)
}

fn ram(size: u32) -> SpaceRef {
    Arc::new(AddrSpace::new_processor("ram", false, size, 1, 1, 0, 1, 0))
}

fn open(name: &str, space: &SpaceRef) -> ObjectLoadImage {
    let path = binary(name);
    let image = ObjectLoadImage::new(path.to_str().expect("utf8 path"), "default");
    image.open().expect("object file opens");
    image.attach_to_space(space.clone());
    image
}

fn symbols(image: &ObjectLoadImage) -> Vec<(String, u64)> {
    let mut res = Vec::new();
    image.open_symbols();
    let mut record = LoadImageFunc::default();
    while image.get_next_symbol(&mut record) {
        res.push((record.name.clone(), record.address.get_offset()));
    }
    image.close_symbols();
    res
}

fn find(list: &[(String, u64)], name: &str) -> u64 {
    list.iter()
        .find(|(symbol, _)| symbol == name)
        .map(|(_, addr)| *addr)
        .unwrap_or_else(|| panic!("missing symbol {name}"))
}

#[test]
fn capability_matches_object_files_only() {
    let capa = &OBJECT_ARCHITECTURE_CAPABILITY;
    assert_eq!(capa.get_name(), "object");
    assert!(capa.is_file_match(binary("x86_64-O0").to_str().expect("utf8 path")));
    assert!(capa.is_file_match(binary("ppc-O2").to_str().expect("utf8 path")));
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/data/decomp/manifest.tsv");
    assert!(!capa.is_file_match(manifest.to_str().expect("utf8 path")));
    assert!(!capa.is_file_match("/nonexistent/file"));
}

#[test]
fn x86_64_symbols_bytes_and_sections() {
    let space = ram(8);
    let image = open("x86_64-O0", &space);
    assert_eq!(image.get_arch_type(), "i386:x86-64:elf64-x86-64");
    assert_eq!(image.inferred_language().as_deref(), Some("x86:LE:64:default:gcc"));
    let list = symbols(&image);
    assert_eq!(find(&list, "_start"), 0x401cf1);
    assert_eq!(find(&list, "main"), 0x4016ed);
    let file = std::fs::read(binary("x86_64-O0")).expect("binary readable");
    let mut buf = [0u8; 16];
    image
        .load_fill(&mut buf, &Address::new(space.clone(), 0x401cf1))
        .expect("entry bytes load");
    assert_eq!(&buf[..], &file[0x1cf1..0x1d01]);
    let mut bss = [0xffu8; 8];
    image
        .load_fill(&mut bss, &Address::new(space.clone(), 0x404140))
        .expect("bss loads");
    assert_eq!(bss, [0u8; 8]);
    let err = image
        .load_fill(&mut buf, &Address::new(space.clone(), 0x10))
        .expect_err("unmapped address fails");
    match err {
        Error::DataUnavail(message) => assert!(message.starts_with("Unable to load 512 bytes at "), "{message}"),
        other => panic!("unexpected error {other:?}"),
    }
    image.open_section_info();
    let mut record = LoadImageSection::default();
    let mut sections = Vec::new();
    loop {
        let more = image.get_next_section(&mut record);
        sections.push((record.address.get_offset(), record.size, record.flags));
        if !more {
            break;
        }
    }
    assert_eq!(
        sections,
        vec![
            (0x401000, 0x1ac9, LoadImageSection::READONLY | LoadImageSection::CODE),
            (0x403000, 0x120, LoadImageSection::READONLY | LoadImageSection::DATA),
            (0x404120, 0x20, LoadImageSection::DATA),
            (0x404140, 0x48, LoadImageSection::NOLOAD),
        ]
    );
    let mut readonly = RangeList::new();
    image.get_readonly(&mut readonly);
    assert!(readonly.in_range(&Address::new(space.clone(), 0x403010), 4));
    assert!(!readonly.in_range(&Address::new(space.clone(), 0x404120), 4));
}

#[test]
fn thumb_symbols_clear_low_bit() {
    let space = ram(4);
    let image = open("thumb-O0", &space);
    assert_eq!(image.get_arch_type(), "arm:elf32-littlearm");
    assert_eq!(image.inferred_language().as_deref(), Some("ARM:LE:32:v8:default"));
    let list = symbols(&image);
    assert_eq!(find(&list, "_start"), 0x10d70);
    assert_eq!(find(&list, "main"), 0x10818);
    let file = std::fs::read(binary("thumb-O0")).expect("binary readable");
    let mut buf = [0u8; 4];
    image
        .load_fill(&mut buf, &Address::new(space.clone(), 0x10))
        .expect("non-allocated section at address zero loads");
    assert_eq!(&buf[..], &file[0x1bec + 0x10..0x1bec + 0x14]);
}

#[test]
fn adjust_vma_moves_sections_and_symbols() {
    let space = ram(8);
    let image = open("x86_64-O0", &space);
    image.adjust_vma_shared(0x1000);
    let list = symbols(&image);
    assert_eq!(find(&list, "main"), 0x4026ed);
    let file = std::fs::read(binary("x86_64-O0")).expect("binary readable");
    let mut buf = [0u8; 8];
    image
        .load_fill(&mut buf, &Address::new(space.clone(), 0x402cf1))
        .expect("adjusted entry loads");
    assert_eq!(&buf[..], &file[0x1cf1..0x1cf9]);
}

#[test]
fn other_architectures_infer_languages() {
    let space = ram(8);
    let expected = [
        ("aarch64-O0", "aarch64:elf64-littleaarch64", "AARCH64:LE:64:v8A:default"),
        ("mips-O0", "mips:elf32-tradbigmips", "MIPS:BE:32:default:default"),
        ("mipsel-O0", "mips:elf32-tradlittlemips", "MIPS:LE:32:default:default"),
        (
            "ppc-O0",
            "powerpc:common:elf32-powerpc",
            "PowerPC:BE:32:default:default",
        ),
        ("riscv64-O0", "riscv:rv64:elf64-littleriscv", "RISCV:LE:64:default:gcc"),
        ("riscv32-O0", "riscv:rv32:elf32-littleriscv", "RISCV:LE:32:default:gcc"),
        ("i686-O0", "i386:elf32-i386", "x86:LE:32:default:gcc"),
    ];
    for (name, archtype, language) in expected {
        let image = open(name, &space);
        assert_eq!(image.get_arch_type(), archtype, "{name}");
        assert_eq!(image.inferred_language().as_deref(), Some(language), "{name}");
        assert!(symbols(&image).iter().any(|(symbol, _)| symbol == "main"), "{name}");
    }
}

#[test]
fn bfd_kludge_table() {
    assert_eq!(
        language_from_arch_type("i386:pei-i386").expect("known"),
        "x86:LE:32:default:windows"
    );
    assert_eq!(
        language_from_arch_type("i386:x86-64:pei-x86-64").expect("known"),
        "x86:LE:64:default:windows"
    );
    assert_eq!(
        language_from_arch_type("i386:x86-64:elf64-x86-64").expect("known"),
        "x86:LE:64:default:gcc"
    );
    assert!(language_from_arch_type("weird").is_err());
}

#[test]
fn not_an_object_file() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/data/decomp/manifest.tsv");
    let image = ObjectLoadImage::new(manifest.to_str().expect("utf8 path"), "default");
    let err = image.open().expect_err("text file is not an object");
    assert!(err.explain().ends_with(" : not in recognized object file format"));
}
