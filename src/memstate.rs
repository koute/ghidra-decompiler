use std::collections::BTreeMap;

use crate::address::{Address, byte_swap, calc_mask};
use crate::error::{Error, Result};
use crate::loadimage::LoadImage;
use crate::pcoderaw::VarnodeData;
use crate::space::{AddrSpace, SpaceRef, SpaceType};
use crate::translate::Translate;

pub struct MemoryBankBase {
    pub wordsize: i32,
    pub pagesize: i32,
    pub space: SpaceRef,
}

impl MemoryBankBase {
    pub fn new(spc: SpaceRef, ws: i32, ps: i32) -> MemoryBankBase {
        MemoryBankBase {
            wordsize: ws,
            pagesize: ps,
            space: spc,
        }
    }

    pub fn construct_value(ptr: &[u8], size: i32, bigendian: bool) -> u64 {
        let mut res: u64 = 0;
        if bigendian {
            for index in 0..size as usize {
                res = res.wrapping_shl(8);
                res = res.wrapping_add(ptr[index] as u64);
            }
        } else {
            for index in (0..size as usize).rev() {
                res = res.wrapping_shl(8);
                res = res.wrapping_add(ptr[index] as u64);
            }
        }
        res
    }

    pub fn deconstruct_value(ptr: &mut [u8], val: u64, size: i32, bigendian: bool) {
        let mut val = val;
        if bigendian {
            for index in (0..size as usize).rev() {
                ptr[index] = (val & 0xff) as u8;
                val >>= 8;
            }
        } else {
            for index in 0..size as usize {
                ptr[index] = (val & 0xff) as u8;
                val >>= 8;
            }
        }
    }
}

pub trait MemoryBank {
    fn base(&self) -> &MemoryBankBase;

    fn insert(&mut self, addr: u64, val: u64) -> Result<()>;

    fn find(&mut self, addr: u64) -> Result<u64>;

    fn get_page(&mut self, addr: u64, res: &mut [u8], skip: i32, size: i32) -> Result<()> {
        let wordsize = self.get_word_size();
        let alignmask = (wordsize as u64).wrapping_sub(1);
        let ptraddr = addr.wrapping_add(skip as u64);
        let endaddr = ptraddr.wrapping_add(size as u64);
        let mut startalign = ptraddr & !alignmask;
        let mut endalign = endaddr & !alignmask;
        if (endaddr & alignmask) != 0 {
            endalign = endalign.wrapping_add(wordsize as u64);
        }
        let bswap = self.get_space().is_big_endian();
        let mut position = 0usize;
        loop {
            let mut curval = self.find(startalign)?;
            if bswap {
                curval = byte_swap(curval, wordsize);
            }
            let bytes = curval.to_le_bytes();
            let mut start = 0usize;
            let mut chunk_size = wordsize as i64;
            if startalign < addr {
                start = (addr - startalign) as usize;
                chunk_size = wordsize as i64 - (addr - startalign) as i64;
            }
            if startalign.wrapping_add(wordsize as u64) > endaddr {
                chunk_size -= startalign.wrapping_add(wordsize as u64).wrapping_sub(endaddr) as i64;
            }
            if chunk_size > 0 {
                let count = chunk_size as usize;
                res[position..position + count].copy_from_slice(&bytes[start..start + count]);
                position += count;
            }
            startalign = startalign.wrapping_add(wordsize as u64);
            if startalign == endalign {
                break;
            }
        }
        Ok(())
    }

    fn set_page(&mut self, addr: u64, val: &[u8], skip: i32, size: i32) -> Result<()> {
        let wordsize = self.get_word_size();
        let alignmask = (wordsize as u64).wrapping_sub(1);
        let ptraddr = addr.wrapping_add(skip as u64);
        let endaddr = ptraddr.wrapping_add(size as u64);
        let mut startalign = ptraddr & !alignmask;
        let mut endalign = endaddr & !alignmask;
        if (endaddr & alignmask) != 0 {
            endalign = endalign.wrapping_add(wordsize as u64);
        }
        let bswap = self.get_space().is_big_endian();
        let mut position = 0usize;
        loop {
            let mut start = 0usize;
            let mut chunk_size = wordsize as i64;
            if startalign < addr {
                start = (addr - startalign) as usize;
                chunk_size = wordsize as i64 - (addr - startalign) as i64;
            }
            if startalign.wrapping_add(wordsize as u64) > endaddr {
                chunk_size -= startalign.wrapping_add(wordsize as u64).wrapping_sub(endaddr) as i64;
            }
            let count = chunk_size.max(0) as usize;
            let mut curval;
            if chunk_size != wordsize as i64 {
                curval = self.find(startalign)?;
                let mut bytes = curval.to_le_bytes();
                bytes[start..start + count].copy_from_slice(&val[position..position + count]);
                curval = u64::from_le_bytes(bytes);
            } else {
                let mut bytes = [0u8; 8];
                let available = val.len().saturating_sub(position).min(8);
                bytes[..available].copy_from_slice(&val[position..position + available]);
                curval = u64::from_le_bytes(bytes);
            }
            if bswap {
                curval = byte_swap(curval, wordsize);
            }
            self.insert(startalign, curval)?;
            position += count;
            startalign = startalign.wrapping_add(wordsize as u64);
            if startalign == endalign {
                break;
            }
        }
        Ok(())
    }

    fn get_word_size(&self) -> i32 {
        self.base().wordsize
    }

    fn get_page_size(&self) -> i32 {
        self.base().pagesize
    }

    fn get_space(&self) -> &SpaceRef {
        &self.base().space
    }

    fn set_value(&mut self, offset: u64, size: i32, val: u64) -> Result<()> {
        let wordsize = self.get_word_size();
        let alignmask = (wordsize as u64).wrapping_sub(1);
        let ind = offset & !alignmask;
        let mut skip = (offset & alignmask) as i32;
        let mut size1 = wordsize - skip;
        let size2;
        let mut gap;
        let mut val1;
        let mut val2;

        if size > size1 {
            size2 = size - size1;
            val1 = self.find(ind)?;
            val2 = self.find(ind.wrapping_add(wordsize as u64))?;
            gap = wordsize - size2;
        } else {
            if size == wordsize {
                self.insert(ind, val)?;
                return Ok(());
            }
            val1 = self.find(ind)?;
            val2 = 0;
            gap = size1 - size;
            size1 = size;
            size2 = 0;
        }

        skip *= 8;
        gap *= 8;
        if self.get_space().is_big_endian() {
            if size2 == 0 {
                val1 &= !(calc_mask(size1).wrapping_shl(gap as u32));
                val1 |= val.wrapping_shl(gap as u32);
                self.insert(ind, val1)?;
            } else {
                val1 &= (!0u64).wrapping_shl((8 * size1) as u32);
                val1 |= val.wrapping_shr((8 * size2) as u32);
                self.insert(ind, val1)?;
                val2 &= (!0u64).wrapping_shr((8 * size2) as u32);
                val2 |= val.wrapping_shl(gap as u32);
                self.insert(ind.wrapping_add(wordsize as u64), val2)?;
            }
        } else if size2 == 0 {
            val1 &= !(calc_mask(size1).wrapping_shl(skip as u32));
            val1 |= val.wrapping_shl(skip as u32);
            self.insert(ind, val1)?;
        } else {
            val1 &= (!0u64).wrapping_shr((8 * size1) as u32);
            val1 |= val.wrapping_shl(skip as u32);
            self.insert(ind, val1)?;
            val2 &= (!0u64).wrapping_shl((8 * size2) as u32);
            val2 |= val.wrapping_shr((8 * size1) as u32);
            self.insert(ind.wrapping_add(wordsize as u64), val2)?;
        }
        Ok(())
    }

    fn get_value(&mut self, offset: u64, size: i32) -> Result<u64> {
        let wordsize = self.get_word_size();
        let alignmask = (wordsize as u64).wrapping_sub(1);
        let ind = offset & !alignmask;
        let skip = (offset & alignmask) as i32;
        let mut size1 = wordsize - skip;
        let size2;
        let gap;
        let val1;
        let val2;
        if size > size1 {
            size2 = size - size1;
            val1 = self.find(ind)?;
            val2 = self.find(ind.wrapping_add(wordsize as u64))?;
            gap = wordsize - size2;
        } else {
            val1 = self.find(ind)?;
            val2 = 0;
            if size == wordsize {
                return Ok(val1);
            }
            gap = size1 - size;
            size1 = size;
            size2 = 0;
        }

        let mut res = if self.get_space().is_big_endian() {
            if size2 == 0 {
                val1.wrapping_shr((8 * gap) as u32)
            } else {
                val1.wrapping_shl((8 * size2) as u32) | val2.wrapping_shr((8 * gap) as u32)
            }
        } else if size2 == 0 {
            val1.wrapping_shr((skip * 8) as u32)
        } else {
            val1.wrapping_shr((skip * 8) as u32) | val2.wrapping_shl((size1 * 8) as u32)
        };
        res &= calc_mask(size);
        Ok(res)
    }

    fn set_chunk(&mut self, offset: u64, size: i32, val: &[u8]) -> Result<()> {
        let pagesize = self.get_page_size();
        let pagemask = (pagesize as u64).wrapping_sub(1);
        let mut offset = offset;
        let mut count = 0i32;
        while count < size {
            let mut cursize = pagesize;
            let offalign = offset & !pagemask;
            let mut skip = 0i32;
            if offalign != offset {
                skip = offset.wrapping_sub(offalign) as i32;
                cursize -= skip;
            }
            if size - count < cursize {
                cursize = size - count;
            }
            self.set_page(offalign, &val[count as usize..], skip, cursize)?;
            count += cursize;
            offset = offset.wrapping_add(cursize as u64);
        }
        Ok(())
    }

    fn get_chunk(&mut self, offset: u64, size: i32, res: &mut [u8]) -> Result<()> {
        let pagesize = self.get_page_size();
        let pagemask = (pagesize as u64).wrapping_sub(1);
        let mut offset = offset;
        let mut count = 0i32;
        while count < size {
            let mut cursize = pagesize;
            let offalign = offset & !pagemask;
            let mut skip = 0i32;
            if offalign != offset {
                skip = offset.wrapping_sub(offalign) as i32;
                cursize -= skip;
            }
            if size - count < cursize {
                cursize = size - count;
            }
            self.get_page(offalign, &mut res[count as usize..], skip, cursize)?;
            count += cursize;
            offset = offset.wrapping_add(cursize as u64);
        }
        Ok(())
    }
}

pub struct MemoryImage<'a> {
    pub base: MemoryBankBase,
    pub loader: &'a dyn LoadImage,
}

impl<'a> MemoryImage<'a> {
    pub fn new(spc: SpaceRef, ws: i32, ps: i32, ld: &'a dyn LoadImage) -> MemoryImage<'a> {
        MemoryImage {
            base: MemoryBankBase::new(spc, ws, ps),
            loader: ld,
        }
    }
}

impl MemoryBank for MemoryImage<'_> {
    fn base(&self) -> &MemoryBankBase {
        &self.base
    }

    fn insert(&mut self, _addr: u64, _val: u64) -> Result<()> {
        Err(Error::Lowlevel("Writing to read-only MemoryBank".to_string()))
    }

    fn find(&mut self, addr: u64) -> Result<u64> {
        let spc = self.get_space().clone();
        let wordsize = self.get_word_size();
        let mut bytes = [0u8; 8];
        let mut res = match self
            .loader
            .load_fill(&mut bytes[..wordsize as usize], &Address::new(spc.clone(), addr))
        {
            Ok(()) => u64::from_le_bytes(bytes),
            Err(Error::DataUnavail(_)) => 0,
            Err(err) => return Err(err),
        };
        if spc.is_big_endian() {
            res = byte_swap(res, wordsize);
        }
        Ok(res)
    }

    fn get_page(&mut self, addr: u64, res: &mut [u8], skip: i32, size: i32) -> Result<()> {
        let spc = self.get_space().clone();
        let target = &mut res[..size as usize];
        match self
            .loader
            .load_fill(target, &Address::new(spc, addr.wrapping_add(skip as u64)))
        {
            Ok(()) => Ok(()),
            Err(Error::DataUnavail(_)) => {
                target.fill(0);
                Ok(())
            }
            Err(err) => Err(err),
        }
    }
}

pub struct MemoryPageOverlay<'a> {
    pub base: MemoryBankBase,
    pub underlie: Option<Box<dyn MemoryBank + 'a>>,
    pub page: BTreeMap<u64, Vec<u8>>,
}

impl<'a> MemoryPageOverlay<'a> {
    pub fn new(spc: SpaceRef, ws: i32, ps: i32, ul: Option<Box<dyn MemoryBank + 'a>>) -> MemoryPageOverlay<'a> {
        MemoryPageOverlay {
            base: MemoryBankBase::new(spc, ws, ps),
            underlie: ul,
            page: BTreeMap::new(),
        }
    }
}

impl MemoryBank for MemoryPageOverlay<'_> {
    fn base(&self) -> &MemoryBankBase {
        &self.base
    }

    fn insert(&mut self, addr: u64, val: u64) -> Result<()> {
        let pagesize = self.get_page_size();
        let pagemask = (pagesize as u64).wrapping_sub(1);
        let pageaddr = addr & !pagemask;
        if !self.page.contains_key(&pageaddr) {
            let mut pagedata = vec![0u8; pagesize as usize];
            if let Some(underlie) = self.underlie.as_mut() {
                underlie.get_page(pageaddr, &mut pagedata, 0, pagesize)?;
            }
            self.page.insert(pageaddr, pagedata);
        }
        let wordsize = self.get_word_size();
        let bigendian = self.get_space().is_big_endian();
        let pageoffset = (addr & pagemask) as usize;
        let pagedata = self.page.get_mut(&pageaddr).expect("missing memory page");
        MemoryBankBase::deconstruct_value(&mut pagedata[pageoffset..], val, wordsize, bigendian);
        Ok(())
    }

    fn find(&mut self, addr: u64) -> Result<u64> {
        let pagemask = (self.get_page_size() as u64).wrapping_sub(1);
        let pageaddr = addr & !pagemask;
        match self.page.get(&pageaddr) {
            None => match self.underlie.as_mut() {
                None => Ok(0),
                Some(underlie) => underlie.find(addr),
            },
            Some(pagedata) => {
                let pageoffset = (addr & pagemask) as usize;
                Ok(MemoryBankBase::construct_value(
                    &pagedata[pageoffset..],
                    self.base.wordsize,
                    self.base.space.is_big_endian(),
                ))
            }
        }
    }

    fn get_page(&mut self, addr: u64, res: &mut [u8], skip: i32, size: i32) -> Result<()> {
        match self.page.get(&addr) {
            None => match self.underlie.as_mut() {
                None => {
                    res[..size as usize].fill(0);
                    Ok(())
                }
                Some(underlie) => underlie.get_page(addr, res, skip, size),
            },
            Some(pagedata) => {
                res[..size as usize].copy_from_slice(&pagedata[skip as usize..(skip + size) as usize]);
                Ok(())
            }
        }
    }

    fn set_page(&mut self, addr: u64, val: &[u8], skip: i32, size: i32) -> Result<()> {
        let pagesize = self.get_page_size();
        if !self.page.contains_key(&addr) {
            let mut pagedata = vec![0u8; pagesize as usize];
            if size != pagesize
                && let Some(underlie) = self.underlie.as_mut()
            {
                underlie.get_page(addr, &mut pagedata, 0, pagesize)?;
            }
            self.page.insert(addr, pagedata);
        }
        let pagedata = self.page.get_mut(&addr).expect("missing memory page");
        pagedata[skip as usize..(skip + size) as usize].copy_from_slice(&val[..size as usize]);
        Ok(())
    }
}

pub struct MemoryHashOverlay<'a> {
    pub base: MemoryBankBase,
    pub underlie: Option<Box<dyn MemoryBank + 'a>>,
    pub alignshift: i32,
    pub collideskip: u64,
    pub address: Vec<u64>,
    pub value: Vec<u64>,
}

impl<'a> MemoryHashOverlay<'a> {
    pub fn new(
        spc: SpaceRef,
        ws: i32,
        ps: i32,
        hashsize: i32,
        ul: Option<Box<dyn MemoryBank + 'a>>,
    ) -> MemoryHashOverlay<'a> {
        let mut remaining = (ws as u32).wrapping_sub(1);
        let mut alignshift = 0;
        while remaining != 0 {
            alignshift += 1;
            remaining >>= 1;
        }
        MemoryHashOverlay {
            base: MemoryBankBase::new(spc, ws, ps),
            underlie: ul,
            alignshift,
            collideskip: 1023,
            address: vec![0xBADBEEF; hashsize as usize],
            value: vec![0; hashsize as usize],
        }
    }
}

impl MemoryBank for MemoryHashOverlay<'_> {
    fn base(&self) -> &MemoryBankBase {
        &self.base
    }

    fn insert(&mut self, addr: u64, val: u64) -> Result<()> {
        let size = self.address.len() as u64;
        let mut offset = (addr >> self.alignshift) % size;
        for _ in 0..size {
            if self.address[offset as usize] == addr {
                self.value[offset as usize] = val;
                return Ok(());
            } else if self.address[offset as usize] == 0xBADBEEF {
                self.address[offset as usize] = addr;
                self.value[offset as usize] = val;
                return Ok(());
            }
            offset = (offset + self.collideskip) % size;
        }
        Err(Error::Lowlevel("Memory state hash_table is full".to_string()))
    }

    fn find(&mut self, addr: u64) -> Result<u64> {
        let size = self.address.len() as u64;
        let mut offset = (addr >> self.alignshift) % size;
        for _ in 0..size {
            if self.address[offset as usize] == addr {
                return Ok(self.value[offset as usize]);
            } else if self.address[offset as usize] == 0xBADBEEF {
                break;
            }
            offset = (offset + self.collideskip) % size;
        }
        match self.underlie.as_mut() {
            None => Ok(0),
            Some(underlie) => underlie.find(addr),
        }
    }
}

pub struct MemoryState<'a> {
    pub trans: &'a dyn Translate,
    pub memspace: Vec<Option<Box<dyn MemoryBank + 'a>>>,
}

impl<'a> MemoryState<'a> {
    pub fn new(trans: &'a dyn Translate) -> MemoryState<'a> {
        MemoryState {
            trans,
            memspace: Vec::new(),
        }
    }

    pub fn get_translate(&self) -> &'a dyn Translate {
        self.trans
    }

    pub fn set_memory_bank(&mut self, bank: Box<dyn MemoryBank + 'a>) {
        let index = bank.get_space().get_index() as usize;
        while index >= self.memspace.len() {
            self.memspace.push(None);
        }
        self.memspace[index] = Some(bank);
    }

    pub fn get_memory_bank(&mut self, spc: &AddrSpace) -> Option<&mut (dyn MemoryBank + 'a)> {
        let index = spc.get_index() as usize;
        match self.memspace.get_mut(index) {
            Some(Some(bank)) => Some(bank.as_mut()),
            _ => None,
        }
    }

    pub fn set_value(&mut self, spc: &AddrSpace, off: u64, size: i32, cval: u64) -> Result<()> {
        match self.get_memory_bank(spc) {
            None => Err(Error::Lowlevel(format!(
                "Setting value for unmapped memory space: {}",
                spc.get_name()
            ))),
            Some(mspace) => mspace.set_value(off, size, cval),
        }
    }

    pub fn get_value(&mut self, spc: &AddrSpace, off: u64, size: i32) -> Result<u64> {
        if spc.get_type() == SpaceType::Constant {
            return Ok(off);
        }
        match self.get_memory_bank(spc) {
            None => Err(Error::Lowlevel(format!(
                "Getting value from unmapped memory space: {}",
                spc.get_name()
            ))),
            Some(mspace) => mspace.get_value(off, size),
        }
    }

    pub fn set_value_by_name(&mut self, nm: &str, cval: u64) -> Result<()> {
        let vdata = self.trans.get_register(nm)?;
        self.set_value_varnode(&vdata, cval)
    }

    pub fn get_value_by_name(&mut self, nm: &str) -> Result<u64> {
        let vdata = self.trans.get_register(nm)?;
        self.get_value_varnode(&vdata)
    }

    pub fn set_value_varnode(&mut self, vn: &VarnodeData, cval: u64) -> Result<()> {
        let space = vn.space.clone().expect("varnode without space");
        self.set_value(&space, vn.offset, vn.size as i32, cval)
    }

    pub fn get_value_varnode(&mut self, vn: &VarnodeData) -> Result<u64> {
        let space = vn.space.clone().expect("varnode without space");
        self.get_value(&space, vn.offset, vn.size as i32)
    }

    pub fn get_chunk(&mut self, res: &mut [u8], spc: &AddrSpace, off: u64, size: i32) -> Result<()> {
        match self.get_memory_bank(spc) {
            None => Err(Error::Lowlevel(format!(
                "Getting chunk from unmapped memory space: {}",
                spc.get_name()
            ))),
            Some(mspace) => mspace.get_chunk(off, size, res),
        }
    }

    pub fn set_chunk(&mut self, val: &[u8], spc: &AddrSpace, off: u64, size: i32) -> Result<()> {
        match self.get_memory_bank(spc) {
            None => Err(Error::Lowlevel(format!(
                "Setting chunk of unmapped memory space: {}",
                spc.get_name()
            ))),
            Some(mspace) => mspace.set_chunk(off, size, val),
        }
    }
}
