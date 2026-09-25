use std::cell::Cell;
use std::collections::BTreeMap;
use std::ops::Bound;

use crate::address::{Address, ELEM_ADDR, MachExtreme};
use crate::block::BlockId;
use crate::error::{Error, Result};
use crate::funcdata::Funcdata;
use crate::marshal::{ATTRIB_CONTENT, ATTRIB_TYPE, Decoder, ElementId, Encoder};
use crate::op::{OpId, PcodeOpBank};

pub const ELEM_COMMENT: ElementId = ElementId::new("comment", 86);
pub const ELEM_COMMENTDB: ElementId = ElementId::new("commentdb", 87);
pub const ELEM_TEXT: ElementId = ElementId::new("text", 88);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CommentKey {
    pub funcaddr: Address,
    pub addr: Address,
    pub uniq: i32,
}

#[derive(Clone, Debug, Default)]
pub struct Comment {
    tp: u32,
    uniq: i32,
    funcaddr: Address,
    addr: Address,
    text: String,
    emitted: Cell<bool>,
}

impl Comment {
    pub const USER1: u32 = 1;
    pub const USER2: u32 = 2;
    pub const USER3: u32 = 4;
    pub const HEADER: u32 = 8;
    pub const WARNING: u32 = 16;
    pub const WARNINGHEADER: u32 = 32;

    pub fn new(tp: u32, fad: &Address, ad: &Address, uq: i32, txt: &str) -> Comment {
        Comment {
            tp,
            uniq: uq,
            funcaddr: fad.clone(),
            addr: ad.clone(),
            text: txt.to_string(),
            emitted: Cell::new(false),
        }
    }

    pub fn new_empty() -> Comment {
        Comment::default()
    }

    pub fn key(&self) -> CommentKey {
        CommentKey {
            funcaddr: self.funcaddr.clone(),
            addr: self.addr.clone(),
            uniq: self.uniq,
        }
    }

    pub fn set_emitted(&self, val: bool) {
        self.emitted.set(val);
    }

    pub fn is_emitted(&self) -> bool {
        self.emitted.get()
    }

    pub fn get_type(&self) -> u32 {
        self.tp
    }

    pub fn get_func_addr(&self) -> &Address {
        &self.funcaddr
    }

    pub fn get_addr(&self) -> &Address {
        &self.addr
    }

    pub fn get_uniq(&self) -> i32 {
        self.uniq
    }

    pub fn get_text(&self) -> &str {
        &self.text
    }

    fn encode_space_attributes(addr: &Address, encoder: &mut dyn Encoder) -> Result<()> {
        let spc = addr
            .get_space()
            .ok_or_else(|| Error::Lowlevel("comment address has no space".to_string()))?;
        spc.encode_attributes(encoder, addr.get_offset())
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        let tpname = Comment::decode_comment_type(self.tp)?;
        encoder.open_element(ELEM_COMMENT);
        encoder.write_string(ATTRIB_TYPE, &tpname);
        encoder.open_element(ELEM_ADDR);
        Comment::encode_space_attributes(&self.funcaddr, encoder)?;
        encoder.close_element(ELEM_ADDR);
        encoder.open_element(ELEM_ADDR);
        Comment::encode_space_attributes(&self.addr, encoder)?;
        encoder.close_element(ELEM_ADDR);
        encoder.open_element(ELEM_TEXT);
        encoder.write_string(ATTRIB_CONTENT, &self.text);
        encoder.close_element(ELEM_TEXT);
        encoder.close_element(ELEM_COMMENT);
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        self.emitted.set(false);
        self.tp = 0;
        let elem_id = decoder.open_element_expect(ELEM_COMMENT)?;
        self.tp = Comment::encode_comment_type(&decoder.read_string_attr(ATTRIB_TYPE)?)?;
        self.funcaddr = Address::decode(decoder)?;
        self.addr = Address::decode(decoder)?;
        let sub_id = decoder.peek_element()?;
        if sub_id != 0 {
            decoder.open_element()?;
            self.text = decoder.read_string_attr(ATTRIB_CONTENT)?;
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)
    }

    pub fn encode_comment_type(name: &str) -> Result<u32> {
        match name {
            "user1" => Ok(Comment::USER1),
            "user2" => Ok(Comment::USER2),
            "user3" => Ok(Comment::USER3),
            "header" => Ok(Comment::HEADER),
            "warning" => Ok(Comment::WARNING),
            "warningheader" => Ok(Comment::WARNINGHEADER),
            _ => Err(Error::Lowlevel(format!("Unknown comment type: {}", name))),
        }
    }

    pub fn decode_comment_type(val: u32) -> Result<String> {
        let name = match val {
            Comment::USER1 => "user1",
            Comment::USER2 => "user2",
            Comment::USER3 => "user3",
            Comment::HEADER => "header",
            Comment::WARNING => "warning",
            Comment::WARNINGHEADER => "warningheader",
            _ => return Err(Error::Lowlevel("Unknown comment type".to_string())),
        };
        Ok(name.to_string())
    }
}

pub fn comment_order(first: &Comment, second: &Comment) -> bool {
    if first.get_func_addr() != second.get_func_addr() {
        return first.get_func_addr() < second.get_func_addr();
    }
    if first.get_addr() != second.get_addr() {
        return first.get_addr() < second.get_addr();
    }
    if first.get_uniq() != second.get_uniq() {
        return first.get_uniq() < second.get_uniq();
    }
    false
}

pub type CommentSet = BTreeMap<CommentKey, Comment>;

pub trait CommentDatabase: Send {
    fn clear(&mut self);

    fn clear_type(&mut self, fad: &Address, tp: u32);

    fn add_comment(&mut self, tp: u32, fad: &Address, ad: &Address, txt: &str);

    fn add_comment_no_duplicate(&mut self, tp: u32, fad: &Address, ad: &Address, txt: &str) -> bool;

    fn delete_comment(&mut self, com: &CommentKey);

    fn get_comment(&self, com: &CommentKey) -> Option<&Comment>;

    fn function_comments(&self, fad: &Address) -> Vec<&Comment>;

    fn encode(&self, encoder: &mut dyn Encoder) -> Result<()>;

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()>;
}

#[derive(Default)]
pub struct CommentDatabaseInternal {
    commentset: CommentSet,
}

impl CommentDatabaseInternal {
    pub fn new() -> CommentDatabaseInternal {
        CommentDatabaseInternal {
            commentset: BTreeMap::new(),
        }
    }

    fn range_key(fad: &Address, extreme: MachExtreme, uniq: i32) -> CommentKey {
        CommentKey {
            funcaddr: fad.clone(),
            addr: Address::extreme(extreme),
            uniq,
        }
    }

    fn function_range(&self, fad: &Address) -> impl DoubleEndedIterator<Item = (&CommentKey, &Comment)> {
        let begin = CommentDatabaseInternal::range_key(fad, MachExtreme::Minimal, 0);
        let end = CommentDatabaseInternal::range_key(fad, MachExtreme::Maximal, 65535);
        self.commentset.range((Bound::Included(begin), Bound::Excluded(end)))
    }

    fn insert_comment(&mut self, com: Comment) {
        let key = com.key();
        self.commentset.entry(key).or_insert(com);
    }
}

impl CommentDatabase for CommentDatabaseInternal {
    fn clear(&mut self) {
        self.commentset.clear();
    }

    fn clear_type(&mut self, fad: &Address, tp: u32) {
        let doomed: Vec<CommentKey> = self
            .function_range(fad)
            .filter(|(_, com)| (com.get_type() & tp) != 0)
            .map(|(key, _)| key.clone())
            .collect();
        for key in doomed {
            self.commentset.remove(&key);
        }
    }

    fn add_comment(&mut self, tp: u32, fad: &Address, ad: &Address, txt: &str) {
        let mut newcom = Comment::new(tp, fad, ad, 65535, txt);
        let search = newcom.key();
        let previous = self
            .commentset
            .range((Bound::Unbounded, Bound::Excluded(&search)))
            .next_back()
            .map(|(_, com)| com);
        let neighbor = match previous {
            Some(com) => Some(com),
            None => self.commentset.values().next(),
        };
        newcom.uniq = 0;
        if let Some(com) = neighbor
            && com.get_addr() == ad
            && com.get_func_addr() == fad
        {
            newcom.uniq = com.get_uniq() + 1;
        }
        self.insert_comment(newcom);
    }

    fn add_comment_no_duplicate(&mut self, tp: u32, fad: &Address, ad: &Address, txt: &str) -> bool {
        let mut newcom = Comment::new(tp, fad, ad, 65535, txt);
        let search = newcom.key();
        newcom.uniq = 0;
        for (_, com) in self
            .commentset
            .range((Bound::Unbounded, Bound::Excluded(&search)))
            .rev()
        {
            if com.get_addr() == ad && com.get_func_addr() == fad {
                if com.get_text() == txt {
                    return false;
                }
                if newcom.uniq == 0 {
                    newcom.uniq = com.get_uniq() + 1;
                }
            } else {
                break;
            }
        }
        self.insert_comment(newcom);
        true
    }

    fn delete_comment(&mut self, com: &CommentKey) {
        self.commentset.remove(com);
    }

    fn get_comment(&self, com: &CommentKey) -> Option<&Comment> {
        self.commentset.get(com)
    }

    fn function_comments(&self, fad: &Address) -> Vec<&Comment> {
        self.function_range(fad).map(|(_, com)| com).collect()
    }

    fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_COMMENTDB);
        for com in self.commentset.values() {
            com.encode(encoder)?;
        }
        encoder.close_element(ELEM_COMMENTDB);
        Ok(())
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_COMMENTDB)?;
        while decoder.peek_element()? != 0 {
            let mut com = Comment::new_empty();
            com.decode(decoder)?;
            self.add_comment(com.get_type(), com.get_func_addr(), com.get_addr(), com.get_text());
        }
        decoder.close_element(elem_id)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Subsort {
    pub index: i32,
    pub order: u32,
    pub pos: u32,
}

impl Subsort {
    pub fn set_header(&mut self, header_type: u32) {
        self.index = -1;
        self.order = header_type;
    }

    pub fn set_block(&mut self, index: i32, ord: u32) {
        self.index = index;
        self.order = ord;
    }
}

#[derive(Default)]
pub struct CommentSorter {
    commmap: BTreeMap<Subsort, CommentKey>,
    start: Option<Subsort>,
    stop: Option<Subsort>,
    opstop: Option<Subsort>,
    display_unplaced_comments: bool,
}

impl CommentSorter {
    pub const HEADER_BASIC: u32 = 0;
    pub const HEADER_UNPLACED: u32 = 1;

    pub fn new() -> CommentSorter {
        CommentSorter {
            commmap: BTreeMap::new(),
            start: None,
            stop: None,
            opstop: None,
            display_unplaced_comments: false,
        }
    }

    fn op_block(data: &Funcdata, op: OpId) -> Result<BlockId> {
        data.op(op)
            .get_parent()
            .ok_or_else(|| Error::Lowlevel("Dead op reaching CommentSorter".to_string()))
    }

    fn find_position(&self, subsort: &mut Subsort, comm: &Comment, data: &Funcdata) -> Result<bool> {
        if comm.get_type() == 0 {
            return Ok(false);
        }
        let fad = data.get_address();
        if (comm.get_type() & (Comment::HEADER | Comment::WARNINGHEADER)) != 0 && comm.get_addr() == fad {
            subsort.set_header(CommentSorter::HEADER_BASIC);
            return Ok(true);
        }
        let tree = &data.obank.optree;
        let opiter = data.obank.begin_main_addr(comm.get_addr());
        let mut backup_op: Option<OpId> = None;
        if let Some(op) = PcodeOpBank::tree_at(tree, &opiter) {
            let block = CommentSorter::op_block(data, op)?;
            if data.block(block).contains(comm.get_addr()) {
                subsort.set_block(data.block(block).get_index(), data.op(op).get_seq_num().get_order());
                return Ok(true);
            }
            if comm.get_addr() == data.op(op).get_addr() {
                backup_op = Some(op);
            }
        }
        let previous = match &opiter {
            Some(key) => tree.range((Bound::Unbounded, Bound::Excluded(key))).next_back(),
            None => tree.iter().next_back(),
        };
        if let Some((_, &op)) = previous {
            let block = CommentSorter::op_block(data, op)?;
            if data.block(block).contains(comm.get_addr()) {
                subsort.set_block(data.block(block).get_index(), 0xffffffff);
                return Ok(true);
            }
        }
        if let Some(op) = backup_op {
            let block = CommentSorter::op_block(data, op)?;
            subsort.set_block(data.block(block).get_index(), data.op(op).get_seq_num().get_order());
            return Ok(true);
        }
        if tree.is_empty() {
            subsort.set_block(0, 0);
            return Ok(true);
        }
        if self.display_unplaced_comments {
            subsort.set_header(CommentSorter::HEADER_UNPLACED);
            return Ok(true);
        }
        Ok(false)
    }

    pub fn setup_function_list(
        &mut self,
        tp: u32,
        data: &Funcdata,
        db: &dyn CommentDatabase,
        display_unplaced: bool,
    ) -> Result<()> {
        self.commmap.clear();
        self.display_unplaced_comments = display_unplaced;
        if tp == 0 {
            return Ok(());
        }
        let fad = data.get_address();
        let mut subsort = Subsort::default();
        for comm in db.function_comments(fad) {
            if self.find_position(&mut subsort, comm, data)? {
                comm.set_emitted(false);
                self.commmap.insert(subsort, comm.key());
                subsort.pos = subsort.pos.wrapping_add(1);
            }
        }
        Ok(())
    }

    fn lower_bound(&self, subsort: &Subsort) -> Option<Subsort> {
        self.commmap
            .range((Bound::Included(subsort), Bound::Unbounded))
            .next()
            .map(|(key, _)| *key)
    }

    fn upper_bound(&self, subsort: &Subsort) -> Option<Subsort> {
        self.commmap
            .range((Bound::Excluded(subsort), Bound::Unbounded))
            .next()
            .map(|(key, _)| *key)
    }

    pub fn setup_block_list(&mut self, data: &Funcdata, bl: BlockId) {
        let mut subsort = Subsort {
            index: data.block(bl).get_index(),
            order: 0,
            pos: 0,
        };
        self.start = self.lower_bound(&subsort);
        subsort.order = 0xffffffff;
        subsort.pos = 0xffffffff;
        self.stop = self.upper_bound(&subsort);
    }

    pub fn setup_op_list(&mut self, data: &Funcdata, op: Option<OpId>) {
        let Some(op) = op else {
            self.opstop = self.stop;
            return;
        };
        let parent = data
            .op(op)
            .get_parent()
            .expect("op in comment sorter has no parent block");
        let subsort = Subsort {
            index: data.block(parent).get_index(),
            order: data.op(op).get_seq_num().get_order(),
            pos: 0xffffffff,
        };
        self.opstop = self.upper_bound(&subsort);
    }

    pub fn setup_header(&mut self, header_type: u32) {
        let mut subsort = Subsort {
            index: -1,
            order: header_type,
            pos: 0,
        };
        self.start = self.lower_bound(&subsort);
        subsort.pos = 0xffffffff;
        self.opstop = self.upper_bound(&subsort);
    }

    pub fn has_next(&self) -> bool {
        self.start != self.opstop
    }

    pub fn get_next(&mut self) -> CommentKey {
        let current = self.start.expect("comment sorter has no next comment");
        let res = self.commmap[&current].clone();
        self.start = self
            .commmap
            .range((Bound::Excluded(current), Bound::Unbounded))
            .next()
            .map(|(key, _)| *key);
        res
    }
}
