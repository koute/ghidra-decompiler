#![allow(dead_code)]

use std::collections::BTreeMap;
use std::sync::Arc;

use ghidra_decompiler::address::Address;
use ghidra_decompiler::error::{Error, Result};
use ghidra_decompiler::marshal::{Decoder, Encoder, PackedDecode, PackedEncode, XmlDecode, XmlEncode};
use ghidra_decompiler::pcoderaw::VarnodeData;
use ghidra_decompiler::space::AddrSpace;
use ghidra_decompiler::translate::{AddrSpaceManager, AssemblyEmit, PcodeEmit, Translate, TranslateBase};
use ghidra_decompiler::xml::DocumentStorage;

#[derive(Default)]
pub struct DummyTranslate {
    pub base: TranslateBase,
    pub registers: BTreeMap<String, VarnodeData>,
}

impl Translate for DummyTranslate {
    fn translate_base(&self) -> &TranslateBase {
        &self.base
    }

    fn translate_base_mut(&mut self) -> &mut TranslateBase {
        &mut self.base
    }

    fn initialize(&mut self, _store: &mut DocumentStorage) -> Result<()> {
        Ok(())
    }

    fn get_register(&self, nm: &str) -> Result<VarnodeData> {
        match self.registers.get(nm) {
            Some(data) => Ok(data.clone()),
            None => Err(Error::Lowlevel("Cannot add register to DummyTranslate".to_string())),
        }
    }

    fn get_register_name(&self, base: &AddrSpace, off: u64, size: i32) -> String {
        for (name, data) in &self.registers {
            let same = data
                .space
                .as_ref()
                .is_some_and(|spc| spc.get_index() == base.get_index());
            if same && data.offset == off && data.size as i32 == size {
                return name.clone();
            }
        }
        String::new()
    }

    fn get_exact_register_name(&self, base: &AddrSpace, off: u64, size: i32) -> String {
        self.get_register_name(base, off, size)
    }

    fn get_all_registers(&self, reglist: &mut BTreeMap<VarnodeData, String>) {
        for (name, data) in &self.registers {
            reglist.insert(data.clone(), name.clone());
        }
    }

    fn get_user_op_names(&self, _res: &mut Vec<String>) {}

    fn instruction_length(&self, _baseaddr: &Address) -> Result<i32> {
        Ok(-1)
    }

    fn one_instruction(&self, _emit: &mut dyn PcodeEmit, _baseaddr: &Address) -> Result<i32> {
        Ok(-1)
    }

    fn print_assembly(&self, _emit: &mut dyn AssemblyEmit, _baseaddr: &Address) -> Result<i32> {
        Ok(-1)
    }
}

pub fn marshal_manager() -> AddrSpaceManager {
    let manager = AddrSpaceManager::new();
    let ram = AddrSpace::new_processor("ram", false, 8, 1, 3, AddrSpace::HASPHYSICAL, 1, 1);
    manager.insert_space(Arc::new(ram)).expect("insert ram space");
    manager
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Format {
    Packed,
    Xml,
}

pub enum AnyEncoder {
    Packed(PackedEncode),
    Xml(XmlEncode),
}

impl AnyEncoder {
    pub fn new(format: Format) -> AnyEncoder {
        match format {
            Format::Packed => AnyEncoder::Packed(PackedEncode::new()),
            Format::Xml => AnyEncoder::Xml(XmlEncode::new(true)),
        }
    }

    pub fn encoder(&mut self) -> &mut dyn Encoder {
        match self {
            AnyEncoder::Packed(encoder) => encoder,
            AnyEncoder::Xml(encoder) => encoder,
        }
    }

    pub fn bytes(&self) -> Vec<u8> {
        match self {
            AnyEncoder::Packed(encoder) => encoder.as_bytes().to_vec(),
            AnyEncoder::Xml(encoder) => encoder.as_bytes().to_vec(),
        }
    }
}

pub fn new_decoder(format: Format, manager: &AddrSpaceManager) -> Box<dyn Decoder + '_> {
    match format {
        Format::Packed => Box::new(PackedDecode::new(Some(manager))),
        Format::Xml => Box::new(XmlDecode::new(Some(manager), 0)),
    }
}

pub fn gunzip(data: &[u8]) -> Vec<u8> {
    assert!(data.len() > 18 && data[0] == 0x1f && data[1] == 0x8b, "not a gzip file");
    let flags = data[3];
    let mut position = 10;
    if flags & 4 != 0 {
        let extra = u16::from_le_bytes([data[position], data[position + 1]]) as usize;
        position += 2 + extra;
    }
    if flags & 8 != 0 {
        while data[position] != 0 {
            position += 1;
        }
        position += 1;
    }
    if flags & 16 != 0 {
        while data[position] != 0 {
            position += 1;
        }
        position += 1;
    }
    if flags & 2 != 0 {
        position += 2;
    }
    miniz_oxide::inflate::decompress_to_vec(&data[position..data.len() - 8]).expect("invalid gzip data")
}
