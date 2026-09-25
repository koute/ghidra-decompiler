use std::collections::BTreeMap;
use std::sync::Arc;

use crate::error::{Error, Result};
use crate::marshal::Decoder;
use crate::pcoderaw::VarnodeData;
use crate::slaformat::*;
use crate::slghsymbol::{SymbolId, SymbolTable, SymbolType};
use crate::space::{AddrSpace, SpaceKind, SpaceRef, SpaceType};
use crate::translate::{AddrSpaceManager, TranslateBase};

pub const MAX_UNIQUE_SIZE: u32 = 256;

#[derive(Clone, Debug, Default)]
pub struct SourceFileIndexer {
    least_unused_index: i32,
    index_to_file: BTreeMap<i32, String>,
    file_to_index: BTreeMap<String, i32>,
}

impl SourceFileIndexer {
    pub fn new() -> SourceFileIndexer {
        SourceFileIndexer::default()
    }

    pub fn index(&mut self, filename: &str) -> i32 {
        if let Some(index) = self.file_to_index.get(filename) {
            return *index;
        }
        self.file_to_index.insert(filename.to_string(), self.least_unused_index);
        self.index_to_file.insert(self.least_unused_index, filename.to_string());
        let res = self.least_unused_index;
        self.least_unused_index += 1;
        res
    }

    pub fn get_index(&mut self, filename: &str) -> i32 {
        *self.file_to_index.entry(filename.to_string()).or_insert(0)
    }

    pub fn get_filename(&mut self, index: i32) -> String {
        self.index_to_file.entry(index).or_default().clone()
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let el = decoder.open_element_expect(ELEM_SOURCEFILES)?;
        while decoder.peek_element()? == ELEM_SOURCEFILE.get_id() {
            let subel = decoder.open_element()?;
            let filename = decoder.read_string_attr(ATTRIB_NAME)?;
            let index = decoder.read_signed_integer_attr(ATTRIB_INDEX)? as i32;
            decoder.close_element(subel)?;
            self.file_to_index.insert(filename.clone(), index);
            self.index_to_file.insert(index, filename);
        }
        decoder.close_element(el)
    }
}

pub type ContextRegistrar<'a> = &'a mut dyn FnMut(&str, i32, i32) -> Result<()>;

#[derive(Clone, Debug, Default)]
pub struct SleighBase {
    pub translate: TranslateBase,
    userop: Vec<String>,
    varnode_xref: BTreeMap<VarnodeData, String>,
    root: Option<SymbolId>,
    pub symtab: Arc<SymbolTable>,
    maxdelayslotbytes: u32,
    unique_allocatemask: u32,
    num_sections: u32,
    indexer: SourceFileIndexer,
}

impl SleighBase {
    pub fn new() -> SleighBase {
        SleighBase::default()
    }

    pub fn is_initialized(&self) -> bool {
        self.root.is_some()
    }

    pub fn get_root(&self) -> Option<SymbolId> {
        self.root
    }

    pub fn get_max_delay_slot_bytes(&self) -> u32 {
        self.maxdelayslotbytes
    }

    pub fn get_unique_allocate_mask(&self) -> u32 {
        self.unique_allocatemask
    }

    pub fn get_num_sections(&self) -> u32 {
        self.num_sections
    }

    pub fn get_indexer(&self) -> &SourceFileIndexer {
        &self.indexer
    }

    fn build_xrefs(&mut self, error_pairs: &mut Vec<String>, register: ContextRegistrar<'_>) -> Result<()> {
        let Some(glb) = self.symtab.get_global_scope() else {
            return Ok(());
        };
        let ids: Vec<SymbolId> = glb.iter().collect();
        for id in ids {
            let sym = self.symtab.get(id);
            match sym.get_type() {
                SymbolType::Varnode => {
                    if let Some(fix) = sym.get_fixed_varnode() {
                        if let Some(existing) = self.varnode_xref.get(fix) {
                            error_pairs.push(sym.get_name().to_string());
                            error_pairs.push(existing.clone());
                        } else {
                            self.varnode_xref.insert(fix.clone(), sym.get_name().to_string());
                        }
                    }
                }
                SymbolType::Userop => {
                    if let crate::slghsymbol::SymbolBody::Userop { index } = &sym.body {
                        let index = *index as usize;
                        while self.userop.len() <= index {
                            self.userop.push(String::new());
                        }
                        self.userop[index] = sym.get_name().to_string();
                    }
                }
                SymbolType::Context => {
                    if let Some(field) = sym.get_pattern_value().and_then(|pv| pv.as_context_field()) {
                        register(sym.get_name(), field.get_start_bit(), field.get_end_bit())?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub fn reregister_context(&self, register: ContextRegistrar<'_>) -> Result<()> {
        let Some(glb) = self.symtab.get_global_scope() else {
            return Ok(());
        };
        for id in glb.iter() {
            let sym = self.symtab.get(id);
            if sym.get_type() == SymbolType::Context
                && let Some(field) = sym.get_pattern_value().and_then(|pv| pv.as_context_field())
            {
                register(sym.get_name(), field.get_start_bit(), field.get_end_bit())?;
            }
        }
        Ok(())
    }

    pub fn get_register(&self, nm: &str) -> Result<VarnodeData> {
        let Some(sym) = self.symtab.find_symbol(nm) else {
            return Err(Error::Sleigh(format!("Unknown register name: {nm}")));
        };
        if sym.get_type() != SymbolType::Varnode {
            return Err(Error::Sleigh(format!("Symbol is not a register: {nm}")));
        }
        Ok(sym.get_fixed_varnode().cloned().unwrap_or_default())
    }

    pub fn get_register_name(&self, base: &AddrSpace, off: u64, size: i32) -> String {
        let key = VarnodeData {
            space: self.translate.manager.get_space(base.get_index()),
            offset: off,
            size: size as u32,
        };
        let target = off.wrapping_add(size as i64 as u64);
        let mut iter = self.varnode_xref.range(..=key).rev();
        let Some((point, name)) = iter.next() else {
            return String::new();
        };
        if point.space.as_ref().map(|spc| spc.get_index()) != Some(base.get_index()) {
            return String::new();
        }
        let offbase = point.offset;
        if point.offset.wrapping_add(point.size as u64) >= target {
            return name.clone();
        }
        for (point, name) in iter {
            if point.space.as_ref().map(|spc| spc.get_index()) != Some(base.get_index()) || point.offset != offbase {
                return String::new();
            }
            if point.offset.wrapping_add(point.size as u64) >= target {
                return name.clone();
            }
        }
        String::new()
    }

    pub fn get_exact_register_name(&self, base: &AddrSpace, off: u64, size: i32) -> String {
        let key = VarnodeData {
            space: self.translate.manager.get_space(base.get_index()),
            offset: off,
            size: size as u32,
        };
        self.varnode_xref.get(&key).cloned().unwrap_or_default()
    }

    pub fn get_all_registers(&self, reglist: &mut BTreeMap<VarnodeData, String>) {
        *reglist = self.varnode_xref.clone();
    }

    pub fn get_user_op_names(&self, res: &mut Vec<String>) {
        *res = self.userop.clone();
    }

    pub fn decode(&mut self, sla: &[u8], register: ContextRegistrar<'_>) -> Result<()> {
        let mut symtab = Arc::unwrap_or_clone(std::mem::take(&mut self.symtab));
        let res = self.decode_with(sla, &mut symtab);
        self.symtab = Arc::new(symtab);
        res?;
        self.root = self
            .symtab
            .get_global_scope()
            .and_then(|scope| scope.find_symbol("instruction"));
        let mut error_pairs = Vec::new();
        self.build_xrefs(&mut error_pairs, register)?;
        if !error_pairs.is_empty() {
            return Err(Error::Sleigh("Duplicate register pairs".to_string()));
        }
        Ok(())
    }

    fn decode_with(&mut self, sla: &[u8], symtab: &mut SymbolTable) -> Result<()> {
        let bytes = decompress_sla(sla)?;
        let mut header = SlaHeader::default();
        let manager = &self.translate.manager;
        let mut decoder = crate::marshal::PackedDecode::new(Some(manager));
        decoder.end_ingest(bytes)?;
        header.read(&mut decoder)?;
        if header.version != FORMAT_VERSION as i64 {
            return Err(Error::Lowlevel(".sla file has wrong format".to_string()));
        }
        let mut big_end = false;
        for item in header.items.iter() {
            if let HeaderItem::BigEndian(val) = item {
                big_end = *val;
            }
        }
        self.indexer.decode(&mut decoder)?;
        decode_sla_spaces(manager, big_end, &mut decoder)?;
        let const_space = manager
            .get_constant_space()
            .ok_or_else(|| Error::Lowlevel("missing constant space".to_string()))?;
        symtab.decode(&mut decoder, &const_space)?;
        decoder.close_element(header.element)?;
        drop(decoder);
        self.apply_header(&header);
        Ok(())
    }

    fn apply_header(&mut self, header: &SlaHeader) {
        self.maxdelayslotbytes = 0;
        self.unique_allocatemask = 0;
        self.num_sections = 0;
        for item in header.items.iter() {
            match item {
                HeaderItem::BigEndian(val) => self.translate.set_big_endian(*val),
                HeaderItem::Align(val) => self.translate.alignment = *val as i32,
                HeaderItem::UniqBase(val) => self.translate.set_unique_base(*val as u32),
                HeaderItem::MaxDelay(val) => self.maxdelayslotbytes = *val as u32,
                HeaderItem::UniqMask(val) => self.unique_allocatemask = *val as u32,
                HeaderItem::NumSections(val) => self.num_sections = *val as u32,
            }
        }
    }

    pub fn get_constant_space(&self) -> Option<SpaceRef> {
        self.translate.manager.get_constant_space()
    }

    pub fn get_unique_space(&self) -> Option<SpaceRef> {
        self.translate.manager.get_unique_space()
    }
}

enum HeaderItem {
    BigEndian(bool),
    Align(i64),
    UniqBase(u64),
    MaxDelay(u64),
    UniqMask(u64),
    NumSections(u64),
}

#[derive(Default)]
struct SlaHeader {
    element: u32,
    version: i64,
    items: Vec<HeaderItem>,
}

impl SlaHeader {
    fn read(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        self.element = decoder.open_element_expect(ELEM_SLEIGH)?;
        let mut attrib = decoder.get_next_attribute_id()?;
        while attrib != 0 {
            if attrib == ATTRIB_BIGENDIAN {
                self.items.push(HeaderItem::BigEndian(decoder.read_bool()?));
            } else if attrib == ATTRIB_ALIGN {
                self.items.push(HeaderItem::Align(decoder.read_signed_integer()?));
            } else if attrib == ATTRIB_UNIQBASE {
                self.items.push(HeaderItem::UniqBase(decoder.read_unsigned_integer()?));
            } else if attrib == ATTRIB_MAXDELAY {
                self.items.push(HeaderItem::MaxDelay(decoder.read_unsigned_integer()?));
            } else if attrib == ATTRIB_UNIQMASK {
                self.items.push(HeaderItem::UniqMask(decoder.read_unsigned_integer()?));
            } else if attrib == ATTRIB_NUMSECTIONS {
                self.items
                    .push(HeaderItem::NumSections(decoder.read_unsigned_integer()?));
            } else if attrib == ATTRIB_VERSION {
                self.version = decoder.read_signed_integer()?;
            }
            attrib = decoder.get_next_attribute_id()?;
        }
        Ok(())
    }
}

fn decode_sla_space(big_endian: bool, decoder: &mut dyn Decoder) -> Result<AddrSpace> {
    let elem_id = decoder.open_element()?;
    let mut index = 0;
    let mut address_size = 0;
    let mut delay = -1;
    let mut name = String::new();
    let mut wordsize = 1;
    let mut big_end = false;
    let mut flags = 0u32;
    loop {
        let attrib_id = decoder.get_next_attribute_id()?;
        if attrib_id == 0 {
            break;
        }
        if attrib_id == ATTRIB_NAME {
            name = decoder.read_string()?;
        }
        if attrib_id == ATTRIB_INDEX {
            index = decoder.read_signed_integer()? as i32;
        } else if attrib_id == ATTRIB_SIZE {
            address_size = decoder.read_signed_integer()? as i32;
        } else if attrib_id == ATTRIB_WORDSIZE {
            wordsize = decoder.read_signed_integer()? as i32;
        } else if attrib_id == ATTRIB_BIGENDIAN {
            big_end = decoder.read_bool()?;
        } else if attrib_id == ATTRIB_DELAY {
            delay = decoder.read_signed_integer()? as i32;
        } else if attrib_id == ATTRIB_PHYSICAL && decoder.read_bool()? {
            flags |= AddrSpace::HASPHYSICAL;
        }
    }
    decoder.close_element(elem_id)?;
    let deadcodedelay = delay;
    if index == 0 {
        return Err(Error::Lowlevel("Expecting index attribute".to_string()));
    }
    if elem_id == ELEM_SPACE_UNIQUE {
        return Ok(AddrSpace::new_unique(big_endian, index, flags));
    }
    if elem_id == ELEM_SPACE_OTHER {
        return Ok(AddrSpace::new_other(index));
    }
    if address_size == 0 || delay == -1 || name.is_empty() {
        return Err(Error::Lowlevel("Expecting size/delay/name attributes".to_string()));
    }
    Ok(AddrSpace::new(
        SpaceKind::Base,
        SpaceType::Processor,
        &name,
        big_end,
        address_size as u32,
        wordsize as u32,
        index,
        flags,
        delay,
        deadcodedelay,
    ))
}

fn decode_sla_spaces(manager: &AddrSpaceManager, big_endian: bool, decoder: &mut dyn Decoder) -> Result<()> {
    manager.insert_space(Arc::new(AddrSpace::new_constant()))?;
    let elem_id = decoder.open_element_expect(ELEM_SPACES)?;
    let defname = decoder.read_string_attr(ATTRIB_DEFAULTSPACE)?;
    while decoder.peek_element()? != 0 {
        let spc = decode_sla_space(big_endian, decoder)?;
        manager.insert_space(Arc::new(spc))?;
    }
    decoder.close_element(elem_id)?;
    let Some(spc) = manager.get_space_by_name(&defname) else {
        return Err(Error::Lowlevel(format!("Bad 'defaultspace' attribute: {defname}")));
    };
    manager.set_default_code_space(spc.get_index())
}
