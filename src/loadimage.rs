use std::sync::Arc;

use crate::address::{Address, RangeList};
use crate::error::{Error, Result};
use crate::space::{AddrSpace, SpaceRef};

#[derive(Clone, Debug, Default)]
pub struct LoadImageFunc {
    pub address: Address,
    pub name: String,
}

#[derive(Clone, Debug, Default)]
pub struct LoadImageSection {
    pub address: Address,
    pub size: u64,
    pub flags: u32,
}

impl LoadImageSection {
    pub const UNALLOC: u32 = 1;
    pub const NOLOAD: u32 = 2;
    pub const CODE: u32 = 4;
    pub const DATA: u32 = 8;
    pub const READONLY: u32 = 16;
}

pub trait LoadImage: Send + Sync {
    fn get_file_name(&self) -> &str;

    fn load_fill(&self, ptr: &mut [u8], addr: &Address) -> Result<()>;

    fn open_symbols(&self) {}

    fn close_symbols(&self) {}

    fn get_next_symbol(&self, _record: &mut LoadImageFunc) -> bool {
        false
    }

    fn open_section_info(&self) {}

    fn close_section_info(&self) {}

    fn get_next_section(&self, _record: &mut LoadImageSection) -> bool {
        false
    }

    fn get_readonly(&self, _list: &mut RangeList) {}

    fn get_arch_type(&self) -> String;

    fn adjust_vma(&mut self, adjust: i64);

    fn load(&self, size: i32, addr: &Address) -> Result<Vec<u8>> {
        let mut buf = vec![0u8; size.max(0) as usize];
        self.load_fill(&mut buf, addr)?;
        Ok(buf)
    }
}

pub type SharedLoadImage = Arc<dyn LoadImage>;

#[derive(Debug, Default)]
pub struct RawLoadImage {
    filename: String,
    vma: u64,
    content: Option<Vec<u8>>,
    spaceid: Option<SpaceRef>,
}

impl RawLoadImage {
    pub fn new(filename: &str) -> RawLoadImage {
        RawLoadImage {
            filename: filename.to_string(),
            vma: 0,
            content: None,
            spaceid: None,
        }
    }

    pub fn from_bytes(filename: &str, bytes: Vec<u8>) -> RawLoadImage {
        RawLoadImage {
            filename: filename.to_string(),
            vma: 0,
            content: Some(bytes),
            spaceid: None,
        }
    }

    pub fn attach_to_space(&mut self, id: SpaceRef) {
        self.spaceid = Some(id);
    }

    pub fn open(&mut self) -> Result<()> {
        if self.content.is_some() {
            return Err(Error::Lowlevel("loadimage is already open".to_string()));
        }
        match std::fs::read(&self.filename) {
            Ok(bytes) => {
                self.content = Some(bytes);
                Ok(())
            }
            Err(_) => Err(Error::Lowlevel(format!(
                "Unable to open raw image file: {}",
                self.filename
            ))),
        }
    }
}

impl LoadImage for RawLoadImage {
    fn get_file_name(&self) -> &str {
        &self.filename
    }

    fn load_fill(&self, ptr: &mut [u8], addr: &Address) -> Result<()> {
        let empty = Vec::new();
        let content = self.content.as_ref().unwrap_or(&empty);
        let filesize = content.len() as u64;
        let mut curaddr = addr.get_offset().wrapping_sub(self.vma);
        let mut offset = 0usize;
        let mut size = ptr.len();
        while size > 0 {
            if curaddr >= filesize {
                if offset == 0 {
                    break;
                }
                ptr[offset..].fill(0);
                return Ok(());
            }
            let mut readsize = size as u64;
            if curaddr.wrapping_add(readsize) > filesize {
                readsize = filesize - curaddr;
            }
            let start = curaddr as usize;
            let count = readsize as usize;
            ptr[offset..offset + count].copy_from_slice(&content[start..start + count]);
            offset += count;
            size -= count;
            curaddr = curaddr.wrapping_add(readsize);
        }
        if size > 0 {
            let mut message = format!("Unable to load {size} bytes at {}", addr.get_shortcut());
            addr.print_raw(&mut message);
            return Err(Error::DataUnavail(message));
        }
        Ok(())
    }

    fn get_arch_type(&self) -> String {
        "unknown".to_string()
    }

    fn adjust_vma(&mut self, adjust: i64) {
        let wordsize = self.spaceid.as_ref().map(|spc| spc.get_word_size()).unwrap_or(1);
        let adjust = AddrSpace::address_to_byte_int(adjust, wordsize);
        self.vma = self.vma.wrapping_add(adjust as u64);
    }
}
