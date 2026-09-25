use std::io::Write;

use miniz_oxide::deflate::core::{CompressorOxide, create_comp_flags_from_zip_params};
use miniz_oxide::inflate::stream::InflateState;
use miniz_oxide::{DataFormat, MZError, MZFlush, MZStatus};

use crate::error::{Error, Result};

pub struct Compress {
    stream: Box<CompressorOxide>,
    pending: Vec<u8>,
    position: usize,
}

impl Compress {
    pub fn new(level: i32) -> Result<Compress> {
        if !(-1..=9).contains(&level) {
            return Err(Error::Lowlevel("Could not initialize deflate stream state".to_string()));
        }
        let flags = create_comp_flags_from_zip_params(level, 15, 0);
        Ok(Compress {
            stream: Box::new(CompressorOxide::new(flags)),
            pending: Vec::new(),
            position: 0,
        })
    }

    pub fn input(&mut self, buffer: &[u8]) {
        self.pending = buffer.to_vec();
        self.position = 0;
    }

    pub fn deflate(&mut self, buffer: &mut [u8], finish: bool) -> Result<i32> {
        let flush = if finish { MZFlush::Finish } else { MZFlush::None };
        let mut written = 0;
        while written < buffer.len() {
            let input = &self.pending[self.position..];
            let result = miniz_oxide::deflate::stream::deflate(&mut self.stream, input, &mut buffer[written..], flush);
            self.position += result.bytes_consumed;
            written += result.bytes_written;
            match result.status {
                Ok(MZStatus::StreamEnd) => break,
                Ok(_) => {}
                Err(MZError::Buf) => break,
                Err(_) => return Err(Error::Lowlevel("Error compressing stream".to_string())),
            }
            if result.bytes_consumed == 0 && result.bytes_written == 0 {
                break;
            }
            if !finish && self.position == self.pending.len() {
                break;
            }
        }
        Ok((buffer.len() - written) as i32)
    }
}

pub struct Decompress {
    stream: Box<InflateState>,
    pending: Vec<u8>,
    position: usize,
    stream_finished: bool,
}

impl Default for Decompress {
    fn default() -> Decompress {
        Decompress::new()
    }
}

impl Decompress {
    pub fn new() -> Decompress {
        Decompress {
            stream: InflateState::new_boxed(DataFormat::Zlib),
            pending: Vec::new(),
            position: 0,
            stream_finished: false,
        }
    }

    pub fn input(&mut self, buffer: &[u8]) {
        self.pending = buffer.to_vec();
        self.position = 0;
    }

    pub fn is_finished(&self) -> bool {
        self.stream_finished
    }

    pub fn inflate(&mut self, buffer: &mut [u8]) -> Result<i32> {
        let mut written = 0;
        while written < buffer.len() {
            let input = &self.pending[self.position..];
            let result =
                miniz_oxide::inflate::stream::inflate(&mut self.stream, input, &mut buffer[written..], MZFlush::None);
            self.position += result.bytes_consumed;
            written += result.bytes_written;
            match result.status {
                Ok(MZStatus::StreamEnd) => {
                    self.stream_finished = true;
                    break;
                }
                Ok(_) => {}
                Err(MZError::Buf) => break,
                Err(_) => return Err(Error::Lowlevel("Error decompressing stream".to_string())),
            }
            if result.bytes_consumed == 0 && result.bytes_written == 0 {
                break;
            }
        }
        Ok((buffer.len() - written) as i32)
    }
}

pub struct CompressBuffer<W: Write> {
    out_stream: W,
    in_buffer: Vec<u8>,
    out_buffer: Vec<u8>,
    compressor: Compress,
}

impl<W: Write> CompressBuffer<W> {
    pub const IN_BUFFER_SIZE: usize = 4096;
    pub const OUT_BUFFER_SIZE: usize = 4096;

    pub fn new(out_stream: W, level: i32) -> Result<CompressBuffer<W>> {
        Ok(CompressBuffer {
            out_stream,
            in_buffer: Vec::with_capacity(Self::IN_BUFFER_SIZE),
            out_buffer: vec![0u8; Self::OUT_BUFFER_SIZE],
            compressor: Compress::new(level)?,
        })
    }

    fn flush_input(&mut self, last_buffer: bool) -> Result<()> {
        self.compressor.input(&self.in_buffer);
        loop {
            let out_avail = self.compressor.deflate(&mut self.out_buffer, last_buffer)? as usize;
            let written = Self::OUT_BUFFER_SIZE - out_avail;
            self.out_stream
                .write_all(&self.out_buffer[..written])
                .map_err(|err| Error::Lowlevel(format!("compressed stream write failed: {err}")))?;
            if out_avail != 0 {
                break;
            }
        }
        self.in_buffer.clear();
        Ok(())
    }

    pub fn write_bytes(&mut self, data: &[u8]) -> Result<()> {
        for &byte in data {
            self.in_buffer.push(byte);
            if self.in_buffer.len() == Self::IN_BUFFER_SIZE {
                self.flush_input(false)?;
            }
        }
        Ok(())
    }

    pub fn sync(&mut self) -> Result<()> {
        self.flush_input(true)
    }

    pub fn into_inner(self) -> W {
        self.out_stream
    }
}
