use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use object::elf::{SHN_LORESERVE, STT_FUNC, STT_GNU_IFUNC, STT_OBJECT};
use object::read::elf::{ElfFile, FileHeader, Sym, SymbolTable};
use object::{Endianness, Object, ObjectSection, ObjectSymbol, ObjectSymbolTable, RelocationTarget, SectionKind};

pub(crate) struct NamedAddress {
    pub(crate) name: String,
    pub(crate) address: u64,
}

pub(crate) struct DataSymbol {
    pub(crate) name: String,
    pub(crate) address: u64,
    pub(crate) size: u64,
}

pub(crate) struct BaseRegister {
    pub(crate) register: &'static str,
    pub(crate) value: u64,
}

#[derive(Default)]
pub(crate) struct ImageSymbols {
    pub(crate) dynamic_functions: Vec<NamedAddress>,
    pub(crate) undefined_names: BTreeSet<String>,
    pub(crate) data_symbols: Vec<DataSymbol>,
    pub(crate) string_sections: Vec<Range<u64>>,
    pub(crate) code_sections: Vec<Range<u64>>,
    pub(crate) entry: Option<u64>,
    pub(crate) got_slot_symbols: BTreeMap<u64, String>,
    pub(crate) got_slot_size: u64,
    pub(crate) stub_sections: Vec<Range<u64>>,
    pub(crate) stub_base_register: Option<BaseRegister>,
}

pub(crate) fn image_symbols(bytes: &[u8]) -> ImageSymbols {
    let Ok(file) = object::File::parse(bytes) else {
        return ImageSymbols::default();
    };
    let symbols = match &file {
        object::File::Elf32(elf) => elf_symbols(elf),
        object::File::Elf64(elf) => elf_symbols(elf),
        _ => ImageSymbols {
            data_symbols: generic_data_symbols(&file),
            ..ImageSymbols::default()
        },
    };
    let section_ranges = |kinds: &[SectionKind]| -> Vec<Range<u64>> {
        file.sections()
            .filter(|section| kinds.contains(&section.kind()))
            .map(|section| section.address()..section.address() + section.size())
            .collect()
    };
    ImageSymbols {
        string_sections: section_ranges(&[SectionKind::ReadOnlyData, SectionKind::ReadOnlyString]),
        code_sections: section_ranges(&[SectionKind::Text]),
        entry: Some(file.entry()).filter(|entry| *entry != 0),
        ..symbols
    }
}

fn elf_symbols<'data, Elf: FileHeader<Endian = Endianness>>(elf: &ElfFile<'data, Elf, &'data [u8]>) -> ImageSymbols {
    let endian = elf.endian();
    let is_arm = elf.architecture() == object::Architecture::Arm;
    let table = elf.elf_dynamic_symbol_table();
    let dynamic_functions = table
        .iter()
        .skip(1)
        .filter(|symbol| matches!(symbol.st_type(), STT_FUNC | STT_GNU_IFUNC) && symbol.st_shndx(endian) != 0)
        .filter_map(|symbol| {
            let name = table.symbol_name(endian, symbol).ok()?;
            let value: u64 = symbol.st_value(endian).into();
            Some(NamedAddress {
                name: String::from_utf8_lossy(name).into_owned(),
                address: if is_arm { value & !1 } else { value },
            })
        })
        .collect();
    let symbol_table = elf.elf_symbol_table();
    let undefined_names = symbol_table
        .iter()
        .skip(1)
        .filter(|symbol| symbol.st_shndx(endian) == 0)
        .filter_map(|symbol| symbol_table.symbol_name(endian, symbol).ok())
        .map(|name| String::from_utf8_lossy(name).into_owned())
        .collect();
    let mut data_addresses = BTreeSet::new();
    let data_symbols = [&symbol_table, &table]
        .into_iter()
        .flat_map(|symbols| elf_data_symbols(symbols, endian))
        .filter(|symbol| data_addresses.insert(symbol.address))
        .collect();
    ImageSymbols {
        dynamic_functions,
        undefined_names,
        data_symbols,
        string_sections: Vec::new(),
        code_sections: Vec::new(),
        entry: None,
        got_slot_symbols: got_slot_symbols(elf),
        got_slot_size: if elf.is_64() { 8 } else { 4 },
        stub_sections: elf
            .sections()
            .filter(|section| {
                section.kind() == SectionKind::Text && section.name().is_ok_and(|name| name.contains("plt"))
            })
            .map(|section| section.address()..section.address() + section.size())
            .collect(),
        stub_base_register: stub_base_register(elf),
    }
}

fn elf_data_symbols<'data, Elf: FileHeader<Endian = Endianness>>(
    symbols: &SymbolTable<'data, Elf, &'data [u8]>,
    endian: Endianness,
) -> Vec<DataSymbol> {
    symbols
        .iter()
        .skip(1)
        .filter(|symbol| {
            let section = symbol.st_shndx(endian);
            symbol.st_type() == STT_OBJECT && section != 0 && section < SHN_LORESERVE
        })
        .filter_map(|symbol| {
            let name = symbols.symbol_name(endian, symbol).ok()?;
            let size: u64 = symbol.st_size(endian).into();
            (size > 0 && !name.is_empty()).then(|| DataSymbol {
                name: String::from_utf8_lossy(name).into_owned(),
                address: symbol.st_value(endian).into(),
                size,
            })
        })
        .collect()
}

fn generic_data_symbols(file: &object::File<'_>) -> Vec<DataSymbol> {
    file.symbols()
        .filter(|symbol| symbol.kind() == object::SymbolKind::Data && symbol.is_definition() && symbol.size() > 0)
        .filter_map(|symbol| {
            Some(DataSymbol {
                name: symbol.name().ok()?.to_string(),
                address: symbol.address(),
                size: symbol.size(),
            })
        })
        .collect()
}

fn got_slot_symbols<'data, Elf: FileHeader<Endian = Endianness>>(
    elf: &ElfFile<'data, Elf, &'data [u8]>,
) -> BTreeMap<u64, String> {
    let Some(symbols) = elf.dynamic_symbol_table() else {
        return BTreeMap::new();
    };
    elf.dynamic_relocations()
        .into_iter()
        .flatten()
        .filter_map(|(slot, relocation)| {
            let RelocationTarget::Symbol(index) = relocation.target() else {
                return None;
            };
            let name = symbols.symbol_by_index(index).ok()?.name().ok()?;
            (!name.is_empty()).then(|| (slot, name.to_string()))
        })
        .collect()
}

fn stub_base_register<'data, Elf: FileHeader<Endian = Endianness>>(
    elf: &ElfFile<'data, Elf, &'data [u8]>,
) -> Option<BaseRegister> {
    if elf.architecture() != object::Architecture::I386 {
        return None;
    }
    let got = elf
        .section_by_name(".got.plt")
        .or_else(|| elf.section_by_name(".got"))?;
    Some(BaseRegister {
        register: "EBX",
        value: got.address(),
    })
}
