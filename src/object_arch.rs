use std::sync::atomic::{AtomicI64, Ordering as AtomicOrdering};
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};

use object::read::elf::{ElfFile, FileHeader, SectionHeader, Sym};
use object::{Endianness, Object, ObjectSection, ObjectSymbol, SectionKind, SymbolKind};

use crate::address::{Address, RangeList};
use crate::architecture::{ATTRIB_ADJUSTVMA, Architecture, ArchitectureCapability, ErrorStream};
use crate::capability::CapabilityPoint;
use crate::error::{Error, Result};
use crate::istream::{Basefield, read_i64};
use crate::loadimage::{LoadImage, LoadImageFunc, LoadImageSection, SharedLoadImage};
use crate::marshal::{ElementId, Encoder};
use crate::sleigh_arch::{
    AdjustableLoadImage, LoaderSlot, SleighArchitecture, SleighArchitectureHooks, SleighCapability,
};
use crate::space::{AddrSpace, SpaceRef};
use crate::xml::{Document, DocumentStorage};

pub const ELEM_BFD_SAVEFILE: ElementId = ElementId::new("bfd_savefile", 238);

const SEC_ALLOC: u32 = 0x1;
const SEC_LOAD: u32 = 0x2;
const SEC_READONLY: u32 = 0x8;
const SEC_CODE: u32 = 0x10;
const SEC_DATA: u32 = 0x20;
const SEC_HAS_CONTENTS: u32 = 0x100;

const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_RELA: u32 = 4;
const SHT_NOBITS: u32 = 8;
const SHT_REL: u32 = 9;
const SHF_WRITE: u64 = 0x1;
const SHF_ALLOC: u64 = 0x2;
const SHF_EXECINSTR: u64 = 0x4;
const STT_FUNC: u8 = 2;
const STT_GNU_IFUNC: u8 = 10;
const SHN_LORESERVE: u16 = 0xff00;
const EM_ARM: u16 = 40;

const BUFFER_SIZE: usize = 512;

#[derive(Clone, Debug, Default)]
struct ObjectSectionRecord {
    vma: u64,
    size: u64,
    file_offset: Option<u64>,
    file_size: u64,
    flags: u32,
}

#[derive(Clone, Debug, Default)]
struct ObjectSymbolRecord {
    name: String,
    value: u64,
    section_relative: bool,
}

#[derive(Clone, Debug, Default)]
struct ParsedObject {
    archtype: String,
    language: Option<String>,
    sections: Vec<ObjectSectionRecord>,
    symbols: Vec<ObjectSymbolRecord>,
}

#[derive(Debug)]
struct ObjectLoadImageState {
    parsed: Option<ParsedObject>,
    spaceid: Option<SpaceRef>,
    adjust: u64,
    bufoffset: u64,
    buffer: Vec<u8>,
    symbols_open: bool,
    cursymbol: usize,
    secinfo: Option<usize>,
}

#[derive(Debug)]
pub struct ObjectLoadImage {
    filename: String,
    target: String,
    data: RwLock<Vec<u8>>,
    state: RwLock<ObjectLoadImageState>,
}

fn arch_type_name(file: &object::File<'_>) -> String {
    let little = file.is_little_endian();
    let format = match file {
        object::File::Elf32(_) => "elf32",
        object::File::Elf64(_) => "elf64",
        object::File::MachO32(_) | object::File::MachO64(_) => "mach-o",
        object::File::Pe32(_) | object::File::Pe64(_) => "pei",
        _ => "unknown",
    };
    let is_pe = format == "pei";
    let is_macho = format == "mach-o";
    let endian_word = if little { "little" } else { "big" };
    match file.architecture() {
        object::Architecture::X86_64 | object::Architecture::X86_64_X32 => {
            if is_pe {
                "i386:x86-64:pei-x86-64".to_string()
            } else if is_macho {
                "i386:x86-64:mach-o-x86-64".to_string()
            } else {
                format!("i386:x86-64:{format}-x86-64")
            }
        }
        object::Architecture::I386 => {
            if is_pe {
                "i386:pei-i386".to_string()
            } else if is_macho {
                "i386:mach-o-i386".to_string()
            } else {
                "i386:elf32-i386".to_string()
            }
        }
        object::Architecture::Arm => {
            if is_pe {
                "arm:pei-arm-little".to_string()
            } else if is_macho {
                "arm:mach-o-arm".to_string()
            } else {
                format!("arm:elf32-{endian_word}arm")
            }
        }
        object::Architecture::Aarch64 | object::Architecture::Aarch64_Ilp32 => {
            if is_pe {
                "aarch64:pei-aarch64-little".to_string()
            } else if is_macho {
                "aarch64:mach-o-arm64".to_string()
            } else {
                format!("aarch64:{format}-{endian_word}aarch64")
            }
        }
        object::Architecture::Mips | object::Architecture::Mips64 | object::Architecture::Mips64_N32 => {
            format!("mips:{format}-trad{endian_word}mips")
        }
        object::Architecture::PowerPc => {
            if little {
                format!("powerpc:common:{format}-powerpcle")
            } else {
                format!("powerpc:common:{format}-powerpc")
            }
        }
        object::Architecture::PowerPc64 => {
            if little {
                format!("powerpc:common64:{format}-powerpcle")
            } else {
                format!("powerpc:common64:{format}-powerpc")
            }
        }
        object::Architecture::Riscv32 => format!("riscv:rv32:{format}-littleriscv"),
        object::Architecture::Riscv64 => format!("riscv:rv64:{format}-littleriscv"),
        object::Architecture::Sparc | object::Architecture::Sparc32Plus => format!("sparc:{format}-sparc"),
        object::Architecture::Sparc64 => format!("sparc:v9:{format}-sparc"),
        other => format!("{}:{format}-{endian_word}", format!("{other:?}").to_lowercase()),
    }
}

fn infer_language(file: &object::File<'_>) -> Option<String> {
    let little = file.is_little_endian();
    let endian = if little { "LE" } else { "BE" };
    let is_pe = matches!(file, object::File::Pe32(_) | object::File::Pe64(_));
    let is_macho = matches!(file, object::File::MachO32(_) | object::File::MachO64(_));
    let language = match file.architecture() {
        object::Architecture::X86_64 => {
            if is_pe {
                "x86:LE:64:default:windows".to_string()
            } else {
                "x86:LE:64:default:gcc".to_string()
            }
        }
        object::Architecture::X86_64_X32 => "x86:LE:64:compat32:gcc".to_string(),
        object::Architecture::I386 => {
            if is_pe {
                "x86:LE:32:default:windows".to_string()
            } else {
                "x86:LE:32:default:gcc".to_string()
            }
        }
        object::Architecture::Arm => {
            if is_pe {
                format!("ARM:{endian}:32:v8:windows")
            } else {
                format!("ARM:{endian}:32:v8:default")
            }
        }
        object::Architecture::Aarch64 => {
            if is_macho {
                "AARCH64:LE:64:AppleSilicon:default".to_string()
            } else if is_pe {
                format!("AARCH64:{endian}:64:v8A:windows")
            } else {
                format!("AARCH64:{endian}:64:v8A:default")
            }
        }
        object::Architecture::Aarch64_Ilp32 => format!("AARCH64:{endian}:32:ilp32:default"),
        object::Architecture::Mips => format!("MIPS:{endian}:32:default:default"),
        object::Architecture::Mips64 => format!("MIPS:{endian}:64:default:default"),
        object::Architecture::Mips64_N32 => format!("MIPS:{endian}:64:64-32addr:default"),
        object::Architecture::PowerPc => format!("PowerPC:{endian}:32:default:default"),
        object::Architecture::PowerPc64 => format!("PowerPC:{endian}:64:default:default"),
        object::Architecture::Riscv32 => "RISCV:LE:32:default:gcc".to_string(),
        object::Architecture::Riscv64 => "RISCV:LE:64:default:gcc".to_string(),
        object::Architecture::Sparc | object::Architecture::Sparc32Plus => "sparc:BE:32:default:default".to_string(),
        object::Architecture::Sparc64 => "sparc:BE:64:default:default".to_string(),
        _ => return None,
    };
    Some(language)
}

fn parse_elf<'data, Elf: FileHeader<Endian = Endianness>>(
    elf: &ElfFile<'data, Elf, &'data [u8]>,
    parsed: &mut ParsedObject,
) {
    let endian = elf.endian();
    let header = elf.elf_header();
    let machine = header.e_machine(endian);
    let table = elf.elf_section_table();
    let shstrndx = header.e_shstrndx(endian) as usize;
    let mut symtab_index: Option<usize> = None;
    let mut symtab_strtab: Option<usize> = None;
    for (index, section) in table.iter().enumerate() {
        if section.sh_type(endian) == SHT_SYMTAB {
            symtab_index = Some(index);
            symtab_strtab = Some(section.sh_link(endian) as usize);
            break;
        }
    }
    let mut regular = vec![false; table.len()];
    for (index, section) in table.iter().enumerate() {
        if index == 0 {
            continue;
        }
        let sh_type = section.sh_type(endian);
        let sh_flags: u64 = section.sh_flags(endian).into();
        if sh_type == SHT_SYMTAB {
            continue;
        }
        if sh_type == SHT_STRTAB && (index == shstrndx || Some(index) == symtab_strtab) {
            continue;
        }
        if (sh_type == SHT_REL || sh_type == SHT_RELA)
            && (sh_flags & SHF_ALLOC) == 0
            && Some(section.sh_link(endian) as usize) == symtab_index
        {
            continue;
        }
        let mut flags = 0u32;
        if (sh_flags & SHF_ALLOC) != 0 {
            flags |= SEC_ALLOC;
            if sh_type != SHT_NOBITS {
                flags |= SEC_LOAD;
            }
        }
        if sh_type != SHT_NOBITS {
            flags |= SEC_HAS_CONTENTS;
        }
        if (sh_flags & SHF_WRITE) == 0 {
            flags |= SEC_READONLY;
        }
        if (sh_flags & SHF_EXECINSTR) != 0 {
            flags |= SEC_CODE;
        } else if (flags & SEC_LOAD) != 0 {
            flags |= SEC_DATA;
        }
        let size: u64 = section.sh_size(endian).into();
        let offset: u64 = section.sh_offset(endian).into();
        regular[index] = true;
        parsed.sections.push(ObjectSectionRecord {
            vma: section.sh_addr(endian).into(),
            size,
            file_offset: if sh_type != SHT_NOBITS { Some(offset) } else { None },
            file_size: if sh_type != SHT_NOBITS { size } else { 0 },
            flags,
        });
    }
    let symbols = elf.elf_symbol_table();
    for symbol in symbols.iter().skip(1) {
        let st_type = symbol.st_type();
        if st_type != STT_FUNC && st_type != STT_GNU_IFUNC {
            continue;
        }
        let name = symbols
            .symbol_name(endian, symbol)
            .map(|bytes| String::from_utf8_lossy(bytes).into_owned())
            .unwrap_or_default();
        let mut value: u64 = symbol.st_value(endian).into();
        if machine == EM_ARM && (value & 1) != 0 {
            value &= !1;
        }
        let shndx = symbol.st_shndx(endian);
        let section_relative =
            shndx != 0 && shndx < SHN_LORESERVE && regular.get(shndx as usize).copied().unwrap_or(false);
        parsed.symbols.push(ObjectSymbolRecord {
            name,
            value,
            section_relative,
        });
    }
}

fn parse_generic(file: &object::File<'_>, parsed: &mut ParsedObject) {
    for section in file.sections() {
        let kind = section.kind();
        let alloc = matches!(
            kind,
            SectionKind::Text
                | SectionKind::Data
                | SectionKind::ReadOnlyData
                | SectionKind::ReadOnlyDataWithRel
                | SectionKind::ReadOnlyString
                | SectionKind::UninitializedData
                | SectionKind::Tls
                | SectionKind::UninitializedTls
        );
        let mut flags = 0u32;
        if alloc {
            flags |= SEC_ALLOC;
            if !matches!(kind, SectionKind::UninitializedData | SectionKind::UninitializedTls) {
                flags |= SEC_LOAD;
            }
        }
        let file_range = section.file_range();
        if file_range.is_some() {
            flags |= SEC_HAS_CONTENTS;
        }
        if matches!(
            kind,
            SectionKind::Text
                | SectionKind::ReadOnlyData
                | SectionKind::ReadOnlyDataWithRel
                | SectionKind::ReadOnlyString
        ) {
            flags |= SEC_READONLY;
        }
        if kind == SectionKind::Text {
            flags |= SEC_CODE;
        } else if (flags & SEC_LOAD) != 0 {
            flags |= SEC_DATA;
        }
        parsed.sections.push(ObjectSectionRecord {
            vma: section.address(),
            size: section.size(),
            file_offset: file_range.map(|(offset, _)| offset),
            file_size: file_range.map(|(_, size)| size).unwrap_or(0),
            flags,
        });
    }
    for symbol in file.symbols() {
        if symbol.kind() != SymbolKind::Text || !symbol.is_definition() {
            continue;
        }
        let name = symbol.name().unwrap_or_default().to_string();
        parsed.symbols.push(ObjectSymbolRecord {
            name,
            value: symbol.address(),
            section_relative: true,
        });
    }
}

fn parse_object(data: &[u8]) -> Option<ParsedObject> {
    let file = object::File::parse(data).ok()?;
    let mut parsed = ParsedObject {
        archtype: arch_type_name(&file),
        language: infer_language(&file),
        ..ParsedObject::default()
    };
    match &file {
        object::File::Elf32(elf) => parse_elf(elf, &mut parsed),
        object::File::Elf64(elf) => parse_elf(elf, &mut parsed),
        object::File::MachO32(_) | object::File::MachO64(_) | object::File::Pe32(_) | object::File::Pe64(_) => {
            parse_generic(&file, &mut parsed)
        }
        _ => return None,
    }
    Some(parsed)
}

fn parse_binary(data: &[u8]) -> ParsedObject {
    ParsedObject {
        archtype: "UNKNOWN!:binary".to_string(),
        language: None,
        sections: vec![ObjectSectionRecord {
            vma: 0,
            size: data.len() as u64,
            file_offset: Some(0),
            file_size: data.len() as u64,
            flags: SEC_ALLOC | SEC_LOAD | SEC_DATA | SEC_HAS_CONTENTS,
        }],
        symbols: Vec::new(),
    }
}

pub fn is_object_file(data: &[u8]) -> bool {
    matches!(
        object::File::parse(data),
        Ok(object::File::Elf32(_)
            | object::File::Elf64(_)
            | object::File::MachO32(_)
            | object::File::MachO64(_)
            | object::File::Pe32(_)
            | object::File::Pe64(_))
    )
}

impl ObjectLoadImage {
    pub fn new(filename: &str, target: &str) -> ObjectLoadImage {
        ObjectLoadImage {
            filename: filename.to_string(),
            target: target.to_string(),
            data: RwLock::new(Vec::new()),
            state: RwLock::new(ObjectLoadImageState {
                parsed: None,
                spaceid: None,
                adjust: 0,
                bufoffset: u64::MAX,
                buffer: vec![0; BUFFER_SIZE],
                symbols_open: false,
                cursymbol: 0,
                secinfo: None,
            }),
        }
    }

    pub fn from_bytes(filename: &str, target: &str, bytes: Vec<u8>) -> Result<ObjectLoadImage> {
        let image = ObjectLoadImage::new(filename, target);
        image.open_bytes(bytes)?;
        Ok(image)
    }

    fn read_state(&self) -> RwLockReadGuard<'_, ObjectLoadImageState> {
        self.state.read().unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    fn write_state(&self) -> RwLockWriteGuard<'_, ObjectLoadImageState> {
        self.state.write().unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    pub fn open(&self) -> Result<()> {
        if self.read_state().parsed.is_some() {
            return Err(Error::Lowlevel("BFD library did not initialize".to_string()));
        }
        let bytes = std::fs::read(&self.filename)
            .map_err(|_| Error::Lowlevel(format!("Unable to open image file: {}", self.filename)))?;
        self.open_bytes(bytes)
    }

    fn open_bytes(&self, bytes: Vec<u8>) -> Result<()> {
        let parsed = if self.target == "binary" {
            parse_binary(&bytes)
        } else {
            match parse_object(&bytes) {
                Some(parsed) => parsed,
                None => {
                    return Err(Error::Lowlevel(format!(
                        "File: {} : not in recognized object file format",
                        self.filename
                    )));
                }
            }
        };
        *self.data.write().unwrap_or_else(|poisoned| poisoned.into_inner()) = bytes;
        self.write_state().parsed = Some(parsed);
        Ok(())
    }

    pub fn attach_to_space(&self, id: SpaceRef) {
        self.write_state().spaceid = Some(id);
    }

    pub fn inferred_language(&self) -> Option<String> {
        self.read_state()
            .parsed
            .as_ref()
            .and_then(|parsed| parsed.language.clone())
    }

    fn find_section(sections: &[ObjectSectionRecord], adjust: u64, offset: u64) -> Option<(usize, u64)> {
        for (index, section) in sections.iter().enumerate() {
            let start = section.vma.wrapping_add(adjust);
            let stop = start.wrapping_add(section.size);
            if offset >= start && offset < stop {
                return Some((index, section.size));
            }
        }
        let mut champ: Option<usize> = None;
        for (index, section) in sections.iter().enumerate() {
            let vma = section.vma.wrapping_add(adjust);
            if vma > offset {
                match champ {
                    None => champ = Some(index),
                    Some(best) => {
                        if vma < sections[best].vma.wrapping_add(adjust) {
                            champ = Some(index);
                        }
                    }
                }
            }
        }
        champ.map(|index| (index, sections[index].size))
    }

    fn section_contents(data: &[u8], section: &ObjectSectionRecord, offset: u64, out: &mut [u8]) {
        out.fill(0);
        let (Some(file_offset), true) = (section.file_offset, (section.flags & SEC_HAS_CONTENTS) != 0) else {
            return;
        };
        if offset >= section.file_size {
            return;
        }
        let available = (section.file_size - offset).min(out.len() as u64) as usize;
        let start = file_offset.wrapping_add(offset) as usize;
        if start >= data.len() {
            return;
        }
        let count = available.min(data.len() - start);
        out[..count].copy_from_slice(&data[start..start + count]);
    }
}

impl LoadImage for ObjectLoadImage {
    fn get_file_name(&self) -> &str {
        &self.filename
    }

    fn load_fill(&self, ptr: &mut [u8], addr: &Address) -> Result<()> {
        let size = ptr.len();
        let mut state = self.write_state();
        let same_space = match (addr.get_space(), state.spaceid.as_ref()) {
            (Some(space), Some(attached)) => space.get_index() == attached.get_index(),
            _ => false,
        };
        if !same_space {
            let name = addr
                .get_space()
                .map(|space| space.get_name().to_string())
                .unwrap_or_default();
            return Err(Error::DataUnavail(format!(
                "Trying to get loadimage bytes from space: {name}"
            )));
        }
        let mut curaddr = addr.get_offset();
        let bufsize = state.buffer.len() as u64;
        if curaddr >= state.bufoffset && curaddr.wrapping_add(size as u64) < state.bufoffset.wrapping_add(bufsize) {
            let start = (curaddr - state.bufoffset) as usize;
            ptr.copy_from_slice(&state.buffer[start..start + size]);
            return Ok(());
        }
        let data = self.data.read().unwrap_or_else(|poisoned| poisoned.into_inner());
        let adjust = state.adjust;
        let state = &mut *state;
        let parsed = state
            .parsed
            .as_ref()
            .ok_or_else(|| Error::Lowlevel("load image is not open".to_string()))?;
        if state.buffer.len() < size {
            state.buffer.resize(size, 0);
        }
        state.bufoffset = curaddr;
        let mut offset = 0usize;
        let mut cursize = state.buffer.len() as u64;
        while cursize > 0 {
            let Some((index, secsize)) = ObjectLoadImage::find_section(&parsed.sections, adjust, curaddr) else {
                if offset == 0 {
                    break;
                }
                state.buffer[offset..].fill(0);
                ptr.copy_from_slice(&state.buffer[..size]);
                return Ok(());
            };
            let section = &parsed.sections[index];
            let vma = section.vma.wrapping_add(adjust);
            let readsize;
            if vma > curaddr {
                if offset == 0 {
                    break;
                }
                readsize = (vma - curaddr).min(cursize);
                state.buffer[offset..offset + readsize as usize].fill(0);
            } else {
                let mut amount = cursize;
                if curaddr.wrapping_add(amount) > vma.wrapping_add(secsize) {
                    amount = vma.wrapping_add(secsize).wrapping_sub(curaddr);
                }
                readsize = amount;
                ObjectLoadImage::section_contents(
                    &data,
                    section,
                    curaddr - vma,
                    &mut state.buffer[offset..offset + readsize as usize],
                );
            }
            offset += readsize as usize;
            cursize -= readsize;
            curaddr = curaddr.wrapping_add(readsize);
        }
        if cursize > 0 {
            let mut message = format!("Unable to load {cursize} bytes at {}", addr.get_shortcut());
            addr.print_raw(&mut message);
            return Err(Error::DataUnavail(message));
        }
        ptr.copy_from_slice(&state.buffer[..size]);
        Ok(())
    }

    fn open_symbols(&self) {
        let mut state = self.write_state();
        state.cursymbol = 0;
        state.symbols_open = true;
    }

    fn close_symbols(&self) {
        let mut state = self.write_state();
        state.cursymbol = 0;
        state.symbols_open = false;
    }

    fn get_next_symbol(&self, record: &mut LoadImageFunc) -> bool {
        let mut state = self.write_state();
        if !state.symbols_open {
            return false;
        }
        let adjust = state.adjust;
        let spaceid = state.spaceid.clone();
        let index = state.cursymbol;
        let Some(symbol) = state
            .parsed
            .as_ref()
            .and_then(|parsed| parsed.symbols.get(index))
            .cloned()
        else {
            return false;
        };
        state.cursymbol += 1;
        record.name = symbol.name;
        let value = if symbol.section_relative {
            symbol.value.wrapping_add(adjust)
        } else {
            symbol.value
        };
        record.address = Address::from_parts(spaceid, value);
        true
    }

    fn open_section_info(&self) {
        let mut state = self.write_state();
        let empty = state.parsed.as_ref().is_none_or(|parsed| parsed.sections.is_empty());
        state.secinfo = if empty { None } else { Some(0) };
    }

    fn close_section_info(&self) {
        self.write_state().secinfo = None;
    }

    fn get_next_section(&self, record: &mut LoadImageSection) -> bool {
        let mut state = self.write_state();
        let Some(index) = state.secinfo else {
            return false;
        };
        let adjust = state.adjust;
        let spaceid = state.spaceid.clone();
        let Some(parsed) = state.parsed.as_ref() else {
            return false;
        };
        let section = parsed.sections[index].clone();
        let total = parsed.sections.len();
        record.address = Address::from_parts(spaceid, section.vma.wrapping_add(adjust));
        record.size = section.size;
        record.flags = 0;
        if (section.flags & SEC_ALLOC) == 0 {
            record.flags |= LoadImageSection::UNALLOC;
        }
        if (section.flags & SEC_LOAD) == 0 {
            record.flags |= LoadImageSection::NOLOAD;
        }
        if (section.flags & SEC_READONLY) != 0 {
            record.flags |= LoadImageSection::READONLY;
        }
        if (section.flags & SEC_CODE) != 0 {
            record.flags |= LoadImageSection::CODE;
        }
        if (section.flags & SEC_DATA) != 0 {
            record.flags |= LoadImageSection::DATA;
        }
        state.secinfo = if index + 1 < total { Some(index + 1) } else { None };
        state.secinfo.is_some()
    }

    fn get_readonly(&self, list: &mut RangeList) {
        let state = self.read_state();
        let (Some(parsed), Some(spaceid)) = (state.parsed.as_ref(), state.spaceid.as_ref()) else {
            return;
        };
        for section in parsed.sections.iter() {
            if (section.flags & SEC_READONLY) != 0 {
                let start = section.vma.wrapping_add(state.adjust);
                if section.size == 0 {
                    continue;
                }
                let stop = start.wrapping_add(section.size).wrapping_sub(1);
                list.insert_range(spaceid, start, stop);
            }
        }
    }

    fn get_arch_type(&self) -> String {
        self.read_state()
            .parsed
            .as_ref()
            .map(|parsed| parsed.archtype.clone())
            .unwrap_or_default()
    }

    fn adjust_vma(&mut self, adjust: i64) {
        self.adjust_vma_shared(adjust);
    }
}

impl AdjustableLoadImage for ObjectLoadImage {
    fn adjust_vma_shared(&self, adjust: i64) {
        let mut state = self.write_state();
        let wordsize = state.spaceid.as_ref().map(|space| space.get_word_size()).unwrap_or(1);
        let bytes = AddrSpace::address_to_byte_int(adjust, wordsize);
        state.adjust = state.adjust.wrapping_add(bytes as u64);
        state.bufoffset = u64::MAX;
    }
}

pub struct ObjectArchitectureCapability;

pub static OBJECT_ARCHITECTURE_CAPABILITY: ObjectArchitectureCapability = ObjectArchitectureCapability;

impl CapabilityPoint for ObjectArchitectureCapability {
    fn initialize(&self) -> Result<()> {
        Ok(())
    }
}

impl ArchitectureCapability for ObjectArchitectureCapability {
    fn get_name(&self) -> &str {
        "object"
    }

    fn build_architecture(
        &self,
        filename: &str,
        target: &str,
        estream: Option<ErrorStream>,
    ) -> Result<Box<Architecture>> {
        Ok(self.build_with_slot(filename, target, estream)?.0)
    }

    fn is_file_match(&self, filename: &str) -> bool {
        match std::fs::read(filename) {
            Ok(bytes) => is_object_file(&bytes),
            Err(_) => false,
        }
    }

    fn is_xml_match(&self, doc: &Document) -> bool {
        doc.get_root().get_name() == "bfd_savefile"
    }
}

impl SleighCapability for ObjectArchitectureCapability {
    fn build_with_slot(
        &self,
        filename: &str,
        target: &str,
        estream: Option<ErrorStream>,
    ) -> Result<(Box<Architecture>, LoaderSlot)> {
        let builder = ObjectArchitecture::new(filename, target, estream);
        let slot = builder.sleigh.loader_slot();
        let mut glb = Box::new(Architecture::new());
        glb.builder = Some(Arc::new(builder));
        Ok((glb, slot))
    }
}

pub struct ObjectArchitecture {
    pub sleigh: SleighArchitecture,
    adjustvma: AtomicI64,
    loader: RwLock<Option<Arc<ObjectLoadImage>>>,
    image_bytes: Option<Vec<u8>>,
}

impl ObjectArchitecture {
    pub fn new(fname: &str, targ: &str, estream: Option<ErrorStream>) -> ObjectArchitecture {
        ObjectArchitecture {
            sleigh: SleighArchitecture::new(fname, targ, estream),
            adjustvma: AtomicI64::new(0),
            loader: RwLock::new(None),
            image_bytes: None,
        }
    }

    pub fn with_bytes(fname: &str, targ: &str, bytes: Vec<u8>) -> ObjectArchitecture {
        ObjectArchitecture {
            image_bytes: Some(bytes),
            ..ObjectArchitecture::new(fname, targ, None)
        }
    }

    fn object_loader(&self) -> Result<Arc<ObjectLoadImage>> {
        self.loader
            .read()
            .expect("poisoned lock")
            .clone()
            .ok_or_else(|| Error::Lowlevel("missing object load image".to_string()))
    }
}

pub fn language_from_arch_type(archtype: &str) -> Result<String> {
    if archtype.contains("efi-app-ia32") || archtype.contains("pe-i386") || archtype.contains("pei-i386") {
        Ok("x86:LE:32:default:windows".to_string())
    } else if archtype.contains("pei-x86-64") {
        Ok("x86:LE:64:default:windows".to_string())
    } else if archtype.contains("sparc") {
        Ok("sparc:BE:32:default:default".to_string())
    } else if archtype.contains("elf64") {
        Ok("x86:LE:64:default:gcc".to_string())
    } else if archtype.contains("elf") {
        Ok("x86:LE:32:default:gcc".to_string())
    } else if archtype.contains("mach-o") {
        Ok("PowerPC:BE:32:default:macosx".to_string())
    } else {
        Err(Error::Lowlevel(format!(
            "Cannot convert bfd target to sleigh target: {archtype}"
        )))
    }
}

impl SleighArchitectureHooks for ObjectArchitecture {
    fn sleigh(&self) -> &SleighArchitecture {
        &self.sleigh
    }

    fn build_loader(&self, glb: &mut Architecture, _store: &mut DocumentStorage) -> Result<()> {
        self.sleigh.collect_spec_files();
        let target = self.sleigh.get_target();
        let format = if target.starts_with("binary") {
            "binary".to_string()
        } else if target.starts_with("default") {
            "default".to_string()
        } else {
            target
        };
        let ldr = match &self.image_bytes {
            Some(bytes) => ObjectLoadImage::from_bytes(&self.sleigh.get_filename(), &format, bytes.clone())?,
            None => {
                let ldr = ObjectLoadImage::new(&self.sleigh.get_filename(), &format);
                ldr.open()?;
                ldr
            }
        };
        if self.adjustvma.load(AtomicOrdering::Relaxed) != 0 {
            ldr.adjust_vma_shared(self.adjustvma.load(AtomicOrdering::Relaxed));
        }
        let loader = Arc::new(ldr);
        *self.loader.write().expect("poisoned lock") = Some(loader.clone());
        self.sleigh.set_adjustable_loader(loader.clone());
        let shared: SharedLoadImage = loader;
        glb.loader = Some(shared);
        Ok(())
    }

    fn resolve_architecture(&self, glb: &mut Architecture) -> Result<()> {
        glb.archid = self.sleigh.get_target();
        if !glb.archid.contains(':') {
            let loader = self.object_loader()?;
            glb.archid = match loader.inferred_language() {
                Some(language) => language,
                None => language_from_arch_type(&loader.get_arch_type())?,
            };
        }
        self.sleigh.resolve_architecture(glb)
    }

    fn post_spec_file(&self, glb: &mut Architecture) -> Result<()> {
        glb.post_spec_file_base()?;
        let loader = self.object_loader()?;
        if let Some(space) = glb.manager.get_default_code_space() {
            loader.attach_to_space(space);
        }
        Ok(())
    }

    fn encode(&self, glb: &Architecture, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_BFD_SAVEFILE);
        self.sleigh.encode_header(encoder);
        encoder.write_unsigned_integer(ATTRIB_ADJUSTVMA, self.adjustvma.load(AtomicOrdering::Relaxed) as u64);
        glb.types
            .as_ref()
            .ok_or_else(|| Error::Lowlevel("missing type factory".to_string()))?
            .encode_core_types(encoder, glb)?;
        glb.encode_base(encoder)?;
        encoder.close_element(ELEM_BFD_SAVEFILE);
        Ok(())
    }

    fn restore_xml(&self, glb: &mut Architecture, store: &mut DocumentStorage) -> Result<()> {
        let Some(el) = store.get_tag("bfd_savefile") else {
            return Err(Error::Lowlevel("Could not find bfd_savefile tag".to_string()));
        };
        self.sleigh.restore_xml_header(&el)?;
        let adjustvma = read_i64(
            el.get_attribute_value("adjustvma")?,
            Basefield::Auto,
            self.adjustvma.load(AtomicOrdering::Relaxed),
        );
        self.adjustvma.store(adjustvma, AtomicOrdering::Relaxed);
        let list = el.get_children();
        let mut iter = 0usize;
        if iter < list.len() && list[iter].get_name() == "coretypes" {
            store.register_tag(&list[iter]);
            iter += 1;
        }
        glb.init(store)?;
        if iter < list.len() {
            store.register_tag(&list[iter]);
            glb.restore_xml_base(store)?;
        }
        Ok(())
    }
}
