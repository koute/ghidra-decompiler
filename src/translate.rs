use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, RwLock, Weak};

use crate::address::{Address, Range, RangeList};
use crate::error::{Error, Result};
use crate::float::FloatFormat;
use crate::istream::{self, Basefield};
use crate::marshal::{ATTRIB_SIZE, ATTRIB_SPACE, AttributeId, Decoder, ElementId};
use crate::opcodes::OpCode;
use crate::pcoderaw::{PcodeOpRaw, VarnodeData};
use crate::space::{
    AddrSpace, CONSTANT_SPACE_INDEX, CONSTANT_SPACE_NAME, JOIN_SPACE_NAME, OTHER_SPACE_INDEX, SpaceRef, SpaceType,
    UNIQUE_SPACE_NAME,
};
use crate::xml::DocumentStorage;

pub const ATTRIB_CODE: AttributeId = AttributeId::new("code", 43);
pub const ATTRIB_CONTAIN: AttributeId = AttributeId::new("contain", 44);
pub const ATTRIB_DEFAULTSPACE: AttributeId = AttributeId::new("defaultspace", 45);
pub const ATTRIB_UNIQBASE: AttributeId = AttributeId::new("uniqbase", 46);

pub const ELEM_OP: ElementId = ElementId::new("op", 27);
pub const ELEM_SLEIGH: ElementId = ElementId::new("sleigh", 28);
pub const ELEM_SPACE: ElementId = ElementId::new("space", 29);
pub const ELEM_SPACEID: ElementId = ElementId::new("spaceid", 30);
pub const ELEM_SPACES: ElementId = ElementId::new("spaces", 31);
pub const ELEM_SPACE_BASE: ElementId = ElementId::new("space_base", 32);
pub const ELEM_SPACE_OTHER: ElementId = ElementId::new("space_other", 33);
pub const ELEM_SPACE_OVERLAY: ElementId = ElementId::new("space_overlay", 34);
pub const ELEM_SPACE_UNIQUE: ElementId = ElementId::new("space_unique", 35);
pub const ELEM_TRUNCATE_SPACE: ElementId = ElementId::new("truncate_space", 36);

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TruncationTag {
    space_name: String,
    size: u32,
}

impl TruncationTag {
    pub fn new(space_name: &str, size: u32) -> TruncationTag {
        TruncationTag {
            space_name: space_name.to_string(),
            size,
        }
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_TRUNCATE_SPACE)?;
        self.space_name = decoder.read_string_attr(ATTRIB_SPACE)?;
        self.size = decoder.read_unsigned_integer_attr(ATTRIB_SIZE)? as u32;
        decoder.close_element(elem_id)
    }

    pub fn get_name(&self) -> &str {
        &self.space_name
    }

    pub fn get_size(&self) -> u32 {
        self.size
    }
}

pub trait PcodeEmit {
    fn dump(&mut self, addr: &Address, opc: OpCode, outvar: Option<&VarnodeData>, vars: &[VarnodeData]) -> Result<()>;

    fn decode_op(&mut self, addr: &Address, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_OP)?;
        let isize = decoder.read_signed_integer_attr(ATTRIB_SIZE)? as i32;
        if isize < 0 {
            return Err(Error::Decoder("Bad <op> size attribute".to_string()));
        }
        let (opcode, outvar, invar) = PcodeOpRaw::decode(decoder, isize)?;
        decoder.close_element(elem_id)?;
        self.dump(addr, opcode, outvar.as_ref(), &invar)
    }
}

pub trait AssemblyEmit {
    fn dump(&mut self, addr: &Address, mnem: &str, body: &str);
}

pub trait AddressResolver: Send + Sync {
    fn resolve(&self, val: u64, sz: i32, point: &Address, full_encoding: &mut u64) -> Address;
}

#[derive(Clone, Debug, Default)]
pub struct JoinRecord {
    pieces: Vec<VarnodeData>,
    unified_space: Option<Weak<AddrSpace>>,
    unified_offset: u64,
    unified_size: u32,
}

impl JoinRecord {
    pub fn num_pieces(&self) -> i32 {
        self.pieces.len() as i32
    }

    pub fn is_float_extension(&self) -> bool {
        self.pieces.len() == 1
    }

    pub fn get_piece(&self, index: i32) -> &VarnodeData {
        &self.pieces[index as usize]
    }

    pub fn get_pieces(&self) -> &[VarnodeData] {
        &self.pieces
    }

    pub fn get_unified(&self) -> VarnodeData {
        VarnodeData {
            space: self.unified_space.as_ref().and_then(Weak::upgrade),
            offset: self.unified_offset,
            size: self.unified_size,
        }
    }

    pub fn get_equivalent_address(&self, offset: u64) -> (Address, i32) {
        if offset < self.unified_offset {
            return (Address::invalid(), -1);
        }
        let mut small_off = offset.wrapping_sub(self.unified_offset) as i32;
        let big_endian = self
            .pieces
            .first()
            .and_then(|piece| piece.space.as_ref())
            .is_some_and(|spc| spc.is_big_endian());
        let count = self.pieces.len() as i32;
        let mut pos: i32;
        if big_endian {
            pos = 0;
            while pos < count {
                let piece_size = self.pieces[pos as usize].size as i32;
                if small_off < piece_size {
                    break;
                }
                small_off -= piece_size;
                pos += 1;
            }
            if pos == count {
                return (Address::invalid(), pos);
            }
        } else {
            pos = count - 1;
            while pos >= 0 {
                let piece_size = self.pieces[pos as usize].size as i32;
                if small_off < piece_size {
                    break;
                }
                small_off -= piece_size;
                pos -= 1;
            }
            if pos < 0 {
                return (Address::invalid(), pos);
            }
        }
        let piece = &self.pieces[pos as usize];
        (
            Address::from_parts(piece.space.clone(), piece.offset.wrapping_add(small_off as i64 as u64)),
            pos,
        )
    }

    pub fn merge_sequence(seq: &mut Vec<VarnodeData>, trans: &dyn Translate) {
        let mut slot = 1;
        while slot < seq.len() {
            if seq[slot - 1].is_contiguous(&seq[slot]) {
                break;
            }
            slot += 1;
        }
        if slot >= seq.len() {
            return;
        }
        let mut res: Vec<VarnodeData> = vec![seq[0].clone()];
        let mut last_is_informal = false;
        for lo in seq.iter().skip(1) {
            let hi = res.last_mut().expect("merge sequence is non-empty");
            if hi.is_contiguous(lo) {
                let big_endian = hi.space.as_ref().is_some_and(|spc| spc.is_big_endian());
                hi.offset = if big_endian { hi.offset } else { lo.offset };
                hi.size = hi.size.wrapping_add(lo.size);
                if let Some(space) = &hi.space
                    && space.get_type() != SpaceType::Spacebase
                {
                    last_is_informal = trans
                        .get_exact_register_name(space, hi.offset, hi.size as i32)
                        .is_empty();
                }
            } else {
                if last_is_informal {
                    break;
                }
                res.push(lo.clone());
            }
        }
        if last_is_informal {
            return;
        }
        *seq = res;
    }
}

#[derive(Debug, Default)]
struct JoinState {
    joinallocate: u64,
    splitset: BTreeMap<(u32, Vec<VarnodeData>), Arc<JoinRecord>>,
    splitlist: Vec<Arc<JoinRecord>>,
    join_space: Option<Weak<AddrSpace>>,
}

#[derive(Debug, Default)]
pub struct JoinTable {
    state: Mutex<JoinState>,
}

impl JoinTable {
    fn lock(&self) -> std::sync::MutexGuard<'_, JoinState> {
        self.state.lock().expect("join table lock poisoned")
    }

    pub fn set_join_space(&self, spc: &SpaceRef) {
        self.lock().join_space = Some(Arc::downgrade(spc));
    }

    pub fn num_records(&self) -> usize {
        self.lock().splitlist.len()
    }

    pub fn find_add_join(&self, pieces: &[VarnodeData], logicalsize: u32) -> Result<Arc<JoinRecord>> {
        if pieces.is_empty() {
            return Err(Error::Lowlevel("Cannot create a join without pieces".to_string()));
        }
        if pieces.len() == 1 && logicalsize == 0 {
            return Err(Error::Lowlevel(
                "Cannot create a single piece join without a logical size".to_string(),
            ));
        }
        let totalsize: u32 = if logicalsize != 0 {
            if pieces.len() != 1 {
                return Err(Error::Lowlevel(
                    "Cannot specify logical size for multiple piece join".to_string(),
                ));
            }
            logicalsize
        } else {
            let sum = pieces.iter().fold(0u32, |accum, piece| accum.wrapping_add(piece.size));
            if sum == 0 {
                return Err(Error::Lowlevel("Cannot create a zero size join".to_string()));
            }
            sum
        };
        let mut state = self.lock();
        let key = (totalsize, pieces.to_vec());
        if let Some(existing) = state.splitset.get(&key) {
            return Ok(existing.clone());
        }
        let roundsize = totalsize.wrapping_add(15) & !0xfu32;
        let record = Arc::new(JoinRecord {
            pieces: pieces.to_vec(),
            unified_space: state.join_space.clone(),
            unified_offset: state.joinallocate,
            unified_size: totalsize,
        });
        state.joinallocate = state.joinallocate.wrapping_add(roundsize as u64);
        state.splitset.insert(key, record.clone());
        state.splitlist.push(record.clone());
        Ok(record)
    }

    pub fn find_join_internal(&self, offset: u64) -> Option<Arc<JoinRecord>> {
        let state = self.lock();
        let mut min: i32 = 0;
        let mut max: i32 = state.splitlist.len() as i32 - 1;
        while min <= max {
            let mid = (min + max) / 2;
            let rec = &state.splitlist[mid as usize];
            let val = rec.unified_offset;
            if val.wrapping_add(rec.unified_size as u64) <= offset {
                min = mid + 1;
            } else if val > offset {
                max = mid - 1;
            } else {
                return Some(rec.clone());
            }
        }
        None
    }

    pub fn find_join(&self, offset: u64) -> Result<Arc<JoinRecord>> {
        let state = self.lock();
        let mut min: i32 = 0;
        let mut max: i32 = state.splitlist.len() as i32 - 1;
        while min <= max {
            let mid = (min + max) / 2;
            let rec = &state.splitlist[mid as usize];
            let val = rec.unified_offset;
            if val == offset {
                return Ok(rec.clone());
            }
            if val < offset {
                min = mid + 1;
            } else {
                max = mid - 1;
            }
        }
        Err(Error::Lowlevel("Unlinked join address".to_string()))
    }

    pub fn renormalize_join_address(&self, addr: &mut Address, size: i32) -> Result<()> {
        let Some(join_record) = self.find_join_internal(addr.get_offset()) else {
            return Err(Error::Lowlevel("Join address not covered by a JoinRecord".to_string()));
        };
        if addr.get_offset() == join_record.unified_offset && size as u32 == join_record.unified_size {
            return Ok(());
        }
        let (addr1, pos1) = join_record.get_equivalent_address(addr.get_offset());
        let (addr2, pos2) =
            join_record.get_equivalent_address(addr.get_offset().wrapping_add((size as i64 - 1) as u64));
        if addr2.is_invalid() {
            return Err(Error::Lowlevel("Join address range not covered".to_string()));
        }
        if pos1 == pos2 {
            *addr = addr1;
            return Ok(());
        }
        let pieces = &join_record.pieces;
        let size_trunc1 = addr1.get_offset().wrapping_sub(pieces[pos1 as usize].offset) as i32;
        let size_trunc2 = (pieces[pos2 as usize].size as i32)
            .wrapping_sub(addr2.get_offset().wrapping_sub(pieces[pos2 as usize].offset) as i32)
            .wrapping_sub(1);
        let mut new_pieces: Vec<VarnodeData> = Vec::new();
        if pos2 < pos1 {
            let mut cursor = pos2;
            while cursor <= pos1 {
                new_pieces.push(pieces[cursor as usize].clone());
                cursor += 1;
            }
            let last = new_pieces.last_mut().expect("renormalized join has pieces");
            last.offset = addr1.get_offset();
            last.size = last.size.wrapping_sub(size_trunc1 as u32);
            let front = new_pieces.first_mut().expect("renormalized join has pieces");
            front.size = front.size.wrapping_sub(size_trunc2 as u32);
        } else {
            let mut cursor = pos1;
            while cursor <= pos2 {
                new_pieces.push(pieces[cursor as usize].clone());
                cursor += 1;
            }
            let front = new_pieces.first_mut().expect("renormalized join has pieces");
            front.offset = addr1.get_offset();
            front.size = front.size.wrapping_sub(size_trunc1 as u32);
            let last = new_pieces.last_mut().expect("renormalized join has pieces");
            last.size = last.size.wrapping_sub(size_trunc2 as u32);
        }
        let new_join_record = self.find_add_join(&new_pieces, 0)?;
        *addr = new_join_record.get_unified().get_addr();
        Ok(())
    }
}

#[derive(Clone, Default)]
struct ManagerState {
    baselist: Vec<Option<SpaceRef>>,
    resolvelist: Vec<Option<Arc<dyn AddressResolver>>>,
    name2space: BTreeMap<String, SpaceRef>,
    shortcut2space: BTreeMap<i32, SpaceRef>,
    constantspace: Option<SpaceRef>,
    defaultcodespace: Option<SpaceRef>,
    defaultdataspace: Option<SpaceRef>,
    iopspace: Option<SpaceRef>,
    fspecspace: Option<SpaceRef>,
    joinspace: Option<SpaceRef>,
    stackspace: Option<SpaceRef>,
    uniqspace: Option<SpaceRef>,
    nohighptr: RangeList,
}

#[derive(Default)]
pub struct AddrSpaceManager {
    state: RwLock<ManagerState>,
    join_table: Arc<JoinTable>,
}

impl Clone for AddrSpaceManager {
    fn clone(&self) -> AddrSpaceManager {
        AddrSpaceManager {
            state: RwLock::new(self.state.read().expect("poisoned lock").clone()),
            join_table: self.join_table.clone(),
        }
    }
}

impl std::fmt::Debug for AddrSpaceManager {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let state = self.state.read().expect("poisoned lock");
        formatter
            .debug_struct("AddrSpaceManager")
            .field(
                "spaces",
                &state
                    .baselist
                    .iter()
                    .flatten()
                    .map(|spc| spc.get_name().to_string())
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

fn shortcut_key(byte: u8) -> i32 {
    byte as i8 as i32
}

impl AddrSpaceManager {
    pub fn new() -> AddrSpaceManager {
        AddrSpaceManager::default()
    }

    pub fn get_join_table(&self) -> &Arc<JoinTable> {
        &self.join_table
    }

    pub fn decode_space(&self, decoder: &mut dyn Decoder) -> Result<AddrSpace> {
        let elem_id = decoder.peek_element()?;
        if elem_id == ELEM_SPACE_BASE {
            AddrSpace::decode_spacebase(decoder)
        } else if elem_id == ELEM_SPACE_UNIQUE {
            AddrSpace::decode_unique(decoder)
        } else if elem_id == ELEM_SPACE_OTHER {
            AddrSpace::decode_other(decoder)
        } else if elem_id == ELEM_SPACE_OVERLAY {
            AddrSpace::decode_overlay(decoder)
        } else if elem_id == ELEM_SPACE {
            AddrSpace::decode_processor(decoder)
        } else {
            Err(Error::Lowlevel("Invalid address space element".to_string()))
        }
    }

    pub fn decode_spaces(&self, decoder: &mut dyn Decoder) -> Result<()> {
        self.insert_space(Arc::new(AddrSpace::new_constant()))?;
        let elem_id = decoder.open_element_expect(ELEM_SPACES)?;
        let defname = decoder.read_string_attr(ATTRIB_DEFAULTSPACE)?;
        while decoder.peek_element()? != 0 {
            let spc = self.decode_space(decoder)?;
            self.insert_space(Arc::new(spc))?;
        }
        decoder.close_element(elem_id)?;
        let Some(spc) = self.get_space_by_name(&defname) else {
            return Err(Error::Lowlevel(format!("Bad 'defaultspace' attribute: {defname}")));
        };
        self.set_default_code_space(spc.get_index())
    }

    pub fn set_default_code_space(&self, index: i32) -> Result<()> {
        let mut state = self.state.write().expect("poisoned lock");
        if state.defaultcodespace.is_some() {
            return Err(Error::Lowlevel("Default space set multiple times".to_string()));
        }
        let found = if index < 0 {
            None
        } else {
            state.baselist.get(index as usize).cloned().flatten()
        };
        let Some(spc) = found else {
            return Err(Error::Lowlevel("Bad index for default space".to_string()));
        };
        state.defaultcodespace = Some(spc.clone());
        state.defaultdataspace = Some(spc);
        Ok(())
    }

    pub fn set_default_data_space(&self, index: i32) -> Result<()> {
        let mut state = self.state.write().expect("poisoned lock");
        if state.defaultcodespace.is_none() {
            return Err(Error::Lowlevel(
                "Default data space must be set after the code space".to_string(),
            ));
        }
        let found = if index < 0 {
            None
        } else {
            state.baselist.get(index as usize).cloned().flatten()
        };
        let Some(spc) = found else {
            return Err(Error::Lowlevel("Bad index for default data space".to_string()));
        };
        state.defaultdataspace = Some(spc);
        Ok(())
    }

    pub fn set_reverse_justified(&self, spc: &AddrSpace) {
        spc.set_flags(AddrSpace::REVERSE_JUSTIFICATION);
    }

    pub fn insert_space(&self, spc: SpaceRef) -> Result<()> {
        let mut state = self.state.write().expect("poisoned lock");
        let name = spc.get_name().to_string();
        let wrong_type = || Error::Lowlevel(format!("Space {name} was initialized with wrong type"));
        let duplicate = || Error::Lowlevel(format!("Space {name} was initialized more than once"));
        match spc.get_type() {
            SpaceType::Constant => {
                if name != CONSTANT_SPACE_NAME {
                    return Err(wrong_type());
                }
                if spc.get_index() != CONSTANT_SPACE_INDEX {
                    return Err(Error::Lowlevel("const space must be assigned index 0".to_string()));
                }
                state.constantspace = Some(spc.clone());
            }
            SpaceType::Internal => {
                if name != UNIQUE_SPACE_NAME {
                    return Err(wrong_type());
                }
                if state.uniqspace.is_some() {
                    return Err(duplicate());
                }
                state.uniqspace = Some(spc.clone());
            }
            SpaceType::Fspec => {
                if name != "fspec" {
                    return Err(wrong_type());
                }
                if state.fspecspace.is_some() {
                    return Err(duplicate());
                }
                state.fspecspace = Some(spc.clone());
            }
            SpaceType::Join => {
                if name != JOIN_SPACE_NAME {
                    return Err(wrong_type());
                }
                if state.joinspace.is_some() {
                    return Err(duplicate());
                }
                state.joinspace = Some(spc.clone());
                self.join_table.set_join_space(&spc);
            }
            SpaceType::Iop => {
                if name != "iop" {
                    return Err(wrong_type());
                }
                if state.iopspace.is_some() {
                    return Err(duplicate());
                }
                state.iopspace = Some(spc.clone());
            }
            SpaceType::Spacebase | SpaceType::Processor => {
                if spc.get_type() == SpaceType::Spacebase && name == "stack" {
                    if state.stackspace.is_some() {
                        return Err(duplicate());
                    }
                    state.stackspace = Some(spc.clone());
                }
                if spc.is_overlay() {
                    if let Some(contain) = spc.get_contain() {
                        contain.set_flags(AddrSpace::OVERLAYBASE);
                    }
                } else if spc.is_other_space() && spc.get_index() != OTHER_SPACE_INDEX {
                    return Err(Error::Lowlevel("OTHER space must be assigned index 1".to_string()));
                }
            }
        }
        let index = spc.get_index();
        if index < 0 {
            return Err(Error::Lowlevel(format!("Space {name} was assigned an invalid index")));
        }
        let slot = index as usize;
        if state.baselist.len() <= slot {
            state.baselist.resize(slot + 1, None);
        }
        if let Some(existing) = &state.baselist[slot] {
            return Err(Error::Lowlevel(format!(
                "Space {name} was assigned id duplicating: {}",
                existing.get_name()
            )));
        }
        if state.name2space.contains_key(&name) {
            return Err(duplicate());
        }
        state.name2space.insert(name, spc.clone());
        state.baselist[slot] = Some(spc.clone());
        AddrSpaceManager::assign_shortcut(&mut state, &spc);
        Ok(())
    }

    fn assign_shortcut(state: &mut ManagerState, spc: &SpaceRef) {
        let current = spc.get_shortcut_byte();
        if current != b' ' {
            state
                .shortcut2space
                .entry(shortcut_key(current))
                .or_insert_with(|| spc.clone());
            return;
        }
        let mut shortcut: i32 = match spc.get_type() {
            SpaceType::Constant => b'#' as i32,
            SpaceType::Processor => {
                if spc.get_name() == "register" {
                    b'%' as i32
                } else {
                    spc.get_name().as_bytes().first().map_or(0, |byte| shortcut_key(*byte))
                }
            }
            SpaceType::Spacebase => b's' as i32,
            SpaceType::Internal => b'u' as i32,
            SpaceType::Fspec => b'f' as i32,
            SpaceType::Join => b'j' as i32,
            SpaceType::Iop => b'i' as i32,
        };
        if (b'A' as i32..=b'Z' as i32).contains(&shortcut) {
            shortcut += 0x20;
        }
        let mut collision_count = 0;
        while state.shortcut2space.contains_key(&shortcut) {
            collision_count += 1;
            if collision_count > 26 {
                spc.set_shortcut(b'z');
                return;
            }
            shortcut = (shortcut + 1) as i8 as i32;
            if shortcut < b'a' as i32 || shortcut > b'z' as i32 {
                shortcut = b'a' as i32;
            }
        }
        state.shortcut2space.insert(shortcut, spc.clone());
        spc.set_shortcut(shortcut as u8);
    }

    pub fn mark_near_pointers(&self, spc: &AddrSpace, size: i32) {
        spc.set_flags(AddrSpace::HAS_NEARPOINTERS);
        if spc.get_minimum_ptr_size() == 0 && spc.get_addr_size() as i32 != size {
            spc.set_minimum_ptr_size(size);
        }
    }

    pub fn copy_spaces(&self, op2: &AddrSpaceManager) -> Result<()> {
        let spaces: Vec<SpaceRef> = op2
            .state
            .read()
            .expect("poisoned lock")
            .baselist
            .iter()
            .flatten()
            .cloned()
            .collect();
        for spc in spaces {
            self.insert_space(spc)?;
        }
        let code_index = op2.get_default_code_space().map_or(-1, |spc| spc.get_index());
        let data_index = op2.get_default_data_space().map_or(-1, |spc| spc.get_index());
        self.set_default_code_space(code_index)?;
        self.set_default_data_space(data_index)
    }

    pub fn add_spacebase_pointer(
        &self,
        basespace: &AddrSpace,
        ptrdata: &VarnodeData,
        trunc_size: i32,
        stack_growth: bool,
    ) -> Result<()> {
        basespace.set_base_register(ptrdata, trunc_size, stack_growth)
    }

    pub fn add_no_high_ptr(&self, rng: &Range) {
        let spc = rng.get_space();
        let flags = spc.get_flags();
        if (flags & AddrSpace::ADDRESSABLE_NONE) != 0 {
            return;
        }
        if (flags & AddrSpace::ADDRESSABLE_ALL) != 0 {
            spc.clear_flags(AddrSpace::ADDRESSABLE_ALL);
        }
        let mut state = self.state.write().expect("poisoned lock");
        state.nohighptr.insert_range(spc, rng.get_first(), rng.get_last());
        let whole = Range::new(spc.clone(), 0, spc.get_highest());
        if state.nohighptr.in_range_range(&whole) {
            spc.set_flags(AddrSpace::ADDRESSABLE_NONE);
        }
    }

    pub fn insert_resolver(&self, spc: &AddrSpace, rsolv: Arc<dyn AddressResolver>) {
        let mut state = self.state.write().expect("poisoned lock");
        let ind = spc.get_index().max(0) as usize;
        while state.resolvelist.len() <= ind {
            state.resolvelist.push(None);
        }
        state.resolvelist[ind] = Some(rsolv);
    }

    pub fn set_infer_ptr_bounds(&self, range: &Range) {
        range
            .get_space()
            .set_pointer_bounds(range.get_first(), range.get_last());
    }

    pub fn get_default_size(&self) -> i32 {
        self.get_default_code_space()
            .map_or(0, |spc| spc.get_addr_size() as i32)
    }

    pub fn get_space_by_name(&self, nm: &str) -> Option<SpaceRef> {
        self.state.read().expect("poisoned lock").name2space.get(nm).cloned()
    }

    pub fn get_space_by_shortcut(&self, sc: char) -> Option<SpaceRef> {
        let key = if (sc as u32) < 0x100 {
            shortcut_key(sc as u32 as u8)
        } else {
            sc as i32
        };
        self.state
            .read()
            .expect("poisoned lock")
            .shortcut2space
            .get(&key)
            .cloned()
    }

    pub fn get_iop_space(&self) -> Option<SpaceRef> {
        self.state.read().expect("poisoned lock").iopspace.clone()
    }

    pub fn get_fspec_space(&self) -> Option<SpaceRef> {
        self.state.read().expect("poisoned lock").fspecspace.clone()
    }

    pub fn get_join_space(&self) -> Option<SpaceRef> {
        self.state.read().expect("poisoned lock").joinspace.clone()
    }

    pub fn get_stack_space(&self) -> Option<SpaceRef> {
        self.state.read().expect("poisoned lock").stackspace.clone()
    }

    pub fn get_unique_space(&self) -> Option<SpaceRef> {
        self.state.read().expect("poisoned lock").uniqspace.clone()
    }

    pub fn get_default_code_space(&self) -> Option<SpaceRef> {
        self.state.read().expect("poisoned lock").defaultcodespace.clone()
    }

    pub fn get_default_data_space(&self) -> Option<SpaceRef> {
        self.state.read().expect("poisoned lock").defaultdataspace.clone()
    }

    pub fn get_constant_space(&self) -> Option<SpaceRef> {
        self.state.read().expect("poisoned lock").constantspace.clone()
    }

    pub fn get_constant(&self, val: u64) -> Address {
        Address::from_parts(self.get_constant_space(), val)
    }

    pub fn high_ptr_possible(&self, loc: &Address, size: i32) -> bool {
        let Some(spc) = loc.get_space() else {
            return true;
        };
        let fl = spc.get_flags() & (AddrSpace::ADDRESSABLE_ALL | AddrSpace::ADDRESSABLE_NONE);
        if fl != 0 {
            return fl == AddrSpace::ADDRESSABLE_ALL;
        }
        !self
            .state
            .read()
            .expect("poisoned lock")
            .nohighptr
            .in_range(loc, size as i64 as u64)
    }

    pub fn create_const_from_space(&self, spc: &AddrSpace) -> Address {
        Address::from_parts(self.get_constant_space(), spc.get_index() as i64 as u64)
    }

    pub fn resolve_constant(
        &self,
        spc: &SpaceRef,
        val: u64,
        sz: i32,
        point: &Address,
        full_encoding: &mut u64,
    ) -> Address {
        let resolver = {
            let state = self.state.read().expect("poisoned lock");
            let ind = spc.get_index();
            if ind >= 0 {
                state.resolvelist.get(ind as usize).cloned().flatten()
            } else {
                None
            }
        };
        if let Some(resolve) = resolver {
            return resolve.resolve(val, sz, point, full_encoding);
        }
        *full_encoding = val;
        let val = AddrSpace::address_to_byte(val, spc.get_word_size());
        let val = spc.wrap_offset(val);
        Address::new(spc.clone(), val)
    }

    pub fn num_spaces(&self) -> i32 {
        self.state.read().expect("poisoned lock").baselist.len() as i32
    }

    pub fn get_space(&self, index: i32) -> Option<SpaceRef> {
        if index < 0 {
            return None;
        }
        self.state
            .read()
            .expect("poisoned lock")
            .baselist
            .get(index as usize)
            .cloned()
            .flatten()
    }

    pub fn get_next_space_in_order(&self, spc: Option<&SpaceRef>) -> Option<SpaceRef> {
        let state = self.state.read().expect("poisoned lock");
        let Some(spc) = spc else {
            return state.baselist.first().cloned().flatten();
        };
        if spc.is_maximal() {
            return None;
        }
        let mut index = (spc.get_index() + 1) as usize;
        while index < state.baselist.len() {
            if let Some(res) = &state.baselist[index] {
                return Some(res.clone());
            }
            index += 1;
        }
        Some(AddrSpace::maximal())
    }

    pub fn find_add_join(&self, pieces: &[VarnodeData], logicalsize: u32) -> Result<Arc<JoinRecord>> {
        self.join_table.find_add_join(pieces, logicalsize)
    }

    pub fn find_join(&self, offset: u64) -> Result<Arc<JoinRecord>> {
        self.join_table.find_join(offset)
    }

    pub fn find_join_internal(&self, offset: u64) -> Option<Arc<JoinRecord>> {
        self.join_table.find_join_internal(offset)
    }

    pub fn set_deadcode_delay(&self, spc: &AddrSpace, delaydelta: i32) {
        spc.set_deadcode_delay(delaydelta);
    }

    pub fn truncate_space(&self, tag: &TruncationTag) -> Result<()> {
        let Some(spc) = self.get_space_by_name(tag.get_name()) else {
            return Err(Error::Lowlevel(format!(
                "Unknown space in <truncate_space> command: {}",
                tag.get_name()
            )));
        };
        spc.truncate_space(tag.get_size());
        Ok(())
    }

    pub fn construct_float_extension_address(
        &self,
        realaddr: &Address,
        realsize: i32,
        logicalsize: i32,
    ) -> Result<Address> {
        if logicalsize == realsize {
            return Ok(realaddr.clone());
        }
        let pieces = vec![VarnodeData {
            space: realaddr.get_space().cloned(),
            offset: realaddr.get_offset(),
            size: realsize as u32,
        }];
        let join = self.find_add_join(&pieces, logicalsize as u32)?;
        Ok(join.get_unified().get_addr())
    }

    pub fn construct_join_address(
        &self,
        translate: &dyn Translate,
        hiaddr: &Address,
        hisz: i32,
        loaddr: &Address,
        losz: i32,
    ) -> Result<Address> {
        let (Some(hispace), Some(lospace)) = (hiaddr.get_space(), loaddr.get_space()) else {
            return Err(Error::Lowlevel("Trying to join in appropriate locations".to_string()));
        };
        let hitp = hispace.get_type();
        let lotp = lospace.get_type();
        let mut usejoinspace = true;
        if (hitp != SpaceType::Spacebase && hitp != SpaceType::Processor)
            || (lotp != SpaceType::Spacebase && lotp != SpaceType::Processor)
        {
            return Err(Error::Lowlevel("Trying to join in appropriate locations".to_string()));
        }
        let default_index = self.get_default_code_space().map(|spc| spc.get_index());
        if hitp == SpaceType::Spacebase
            || lotp == SpaceType::Spacebase
            || Some(hispace.get_index()) == default_index
            || Some(lospace.get_index()) == default_index
        {
            usejoinspace = false;
        }
        if hiaddr.is_contiguous(hisz, loaddr, losz) {
            if !usejoinspace {
                if hiaddr.is_big_endian() {
                    return Ok(hiaddr.clone());
                }
                return Ok(loaddr.clone());
            } else if hiaddr.is_big_endian() {
                if !translate
                    .get_register_name(hispace, hiaddr.get_offset(), hisz + losz)
                    .is_empty()
                {
                    return Ok(hiaddr.clone());
                }
            } else if !translate
                .get_register_name(lospace, loaddr.get_offset(), hisz + losz)
                .is_empty()
            {
                return Ok(loaddr.clone());
            }
        }
        let pieces = vec![
            VarnodeData {
                space: Some(hispace.clone()),
                offset: hiaddr.get_offset(),
                size: hisz as u32,
            },
            VarnodeData {
                space: Some(lospace.clone()),
                offset: loaddr.get_offset(),
                size: losz as u32,
            },
        ];
        let join = self.find_add_join(&pieces, 0)?;
        Ok(join.get_unified().get_addr())
    }

    pub fn construct_wrapping_address(&self, addr: &Address, size: i32) -> Result<Address> {
        let Some(spc) = addr.get_space() else {
            return Ok(addr.clone());
        };
        if !spc.is_heritaged() {
            return Ok(addr.clone());
        }
        let dist = spc.get_highest().wrapping_sub(addr.get_offset()).wrapping_add(1);
        if size as i64 as u64 <= dist {
            return Ok(addr.clone());
        }
        if !spc.allows_wrapped_range() {
            return Err(Error::Lowlevel(format!(
                "Trying to construct memory range beyond end of address space: {}",
                spc.get_name()
            )));
        }
        let sizehi = dist as i32;
        let sizelo = size - sizehi;
        let high_index = if spc.is_big_endian() { 0 } else { 1 };
        let mut pieces = vec![VarnodeData::default(), VarnodeData::default()];
        pieces[high_index] = VarnodeData {
            space: Some(spc.clone()),
            offset: addr.get_offset(),
            size: sizehi as u32,
        };
        pieces[1 - high_index] = VarnodeData {
            space: Some(spc.clone()),
            offset: 0,
            size: sizelo as u32,
        };
        let join = self.find_add_join(&pieces, 0)?;
        Ok(join.get_unified().get_addr())
    }

    pub fn renormalize_join_address(&self, addr: &mut Address, size: i32) -> Result<()> {
        self.join_table.renormalize_join_address(addr, size)
    }

    pub fn strip_join_piece(&self, join: &JoinRecord, index: i32) -> Result<VarnodeData> {
        let (start, end) = if index == 0 {
            (1, join.num_pieces() - 1)
        } else if index == join.num_pieces() - 1 {
            (0, join.num_pieces() - 2)
        } else {
            return Err(Error::Lowlevel("Stripping middle piece from JoinRecord".to_string()));
        };
        if start == end {
            return Ok(join.get_piece(start).clone());
        }
        let mut new_pieces = Vec::new();
        let mut slot = start;
        while slot <= end {
            new_pieces.push(join.get_piece(slot).clone());
            slot += 1;
        }
        let new_join_record = self.find_add_join(&new_pieces, 0)?;
        Ok(new_join_record.get_unified())
    }

    pub fn parse_address_simple(&self, val: &str) -> Result<Address> {
        let (spc, mut col) = match val.find(':') {
            None => (self.get_default_data_space(), 0),
            Some(col) => {
                let spc_name = &val[..col];
                let Some(spc) = self.get_space_by_name(spc_name) else {
                    return Err(Error::Lowlevel(format!("Unknown address space: {spc_name}")));
                };
                (Some(spc), col + 1)
            }
        };
        let bytes = val.as_bytes();
        if col + 2 <= bytes.len() && bytes[col] == b'0' && bytes[col + 1] == b'x' {
            col += 2;
        }
        let off = istream::read_u64(&val[col..], Basefield::Hex, 0);
        let Some(spc) = spc else {
            return Err(Error::Lowlevel("No default data space".to_string()));
        };
        let offset = AddrSpace::address_to_byte(off, spc.get_word_size());
        Ok(Address::new(spc, offset))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UniqueLayout {
    RuntimeBooleanInvert = 0,
    RuntimeReturnLocation = 0x80,
    RuntimeBitrangeEa = 0x100,
    Inject = 0x200,
    Analysis = 0x10000000,
}

#[derive(Clone, Debug)]
pub struct TranslateBase {
    pub manager: AddrSpaceManager,
    target_isbigendian: bool,
    unique_base: u32,
    pub alignment: i32,
    pub floatformats: Vec<FloatFormat>,
}

impl Default for TranslateBase {
    fn default() -> TranslateBase {
        TranslateBase {
            manager: AddrSpaceManager::new(),
            target_isbigendian: false,
            unique_base: 0,
            alignment: 1,
            floatformats: Vec::new(),
        }
    }
}

impl TranslateBase {
    pub fn new() -> TranslateBase {
        TranslateBase::default()
    }

    pub fn set_big_endian(&mut self, val: bool) {
        self.target_isbigendian = val;
    }

    pub fn set_unique_base(&mut self, val: u32) {
        if val > self.unique_base {
            self.unique_base = val;
        }
    }

    pub fn set_default_float_formats(&mut self) {
        if self.floatformats.is_empty() {
            self.floatformats.push(FloatFormat::new(4));
            self.floatformats.push(FloatFormat::new(8));
        }
    }

    pub fn is_big_endian(&self) -> bool {
        self.target_isbigendian
    }

    pub fn get_float_format(&self, size: i32) -> Option<&FloatFormat> {
        self.floatformats.iter().find(|format| format.get_size() == size)
    }

    pub fn get_alignment(&self) -> i32 {
        self.alignment
    }

    pub fn get_unique_base(&self) -> u32 {
        self.unique_base
    }

    pub fn get_unique_start(&self, layout: UniqueLayout) -> u32 {
        if layout != UniqueLayout::Analysis {
            (layout as u32).wrapping_add(self.unique_base)
        } else {
            layout as u32
        }
    }
}

pub trait Translate: Send + Sync {
    fn translate_base(&self) -> &TranslateBase;

    fn translate_base_mut(&mut self) -> &mut TranslateBase;

    fn initialize(&mut self, store: &mut DocumentStorage) -> Result<()>;

    fn register_context(&mut self, _name: &str, _sbit: i32, _ebit: i32) -> Result<()> {
        Ok(())
    }

    fn set_context_default(&mut self, _name: &str, _val: u32) -> Result<()> {
        Ok(())
    }

    fn allow_context_set(&self, _val: bool) {}

    fn get_register(&self, nm: &str) -> Result<VarnodeData>;

    fn get_register_name(&self, base: &AddrSpace, off: u64, size: i32) -> String;

    fn get_exact_register_name(&self, base: &AddrSpace, off: u64, size: i32) -> String;

    fn get_all_registers(&self, reglist: &mut BTreeMap<VarnodeData, String>);

    fn get_user_op_names(&self, res: &mut Vec<String>);

    fn instruction_length(&self, baseaddr: &Address) -> Result<i32>;

    fn one_instruction(&self, emit: &mut dyn PcodeEmit, baseaddr: &Address) -> Result<i32>;

    fn print_assembly(&self, emit: &mut dyn AssemblyEmit, baseaddr: &Address) -> Result<i32>;

    fn manager(&self) -> &AddrSpaceManager {
        &self.translate_base().manager
    }

    fn set_default_float_formats(&mut self) {
        self.translate_base_mut().set_default_float_formats();
    }

    fn is_big_endian(&self) -> bool {
        self.translate_base().is_big_endian()
    }

    fn get_float_format(&self, size: i32) -> Option<&FloatFormat> {
        self.translate_base().get_float_format(size)
    }

    fn get_alignment(&self) -> i32 {
        self.translate_base().get_alignment()
    }

    fn get_unique_base(&self) -> u32 {
        self.translate_base().get_unique_base()
    }

    fn get_unique_start(&self, layout: UniqueLayout) -> u32 {
        self.translate_base().get_unique_start(layout)
    }

    fn as_sleigh(&self) -> Option<&crate::sleigh::Sleigh> {
        None
    }
}
