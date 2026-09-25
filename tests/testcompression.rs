use ghidra_decompiler::compression::{Compress, CompressBuffer, Decompress};
use ghidra_decompiler::slaformat::decompress_sla;

const ZLIB_STREAM: &str = "78da0bc94855282ccd4cce56482aca2fcf5348cbaf50c82acd2d2856c82f4b2d5228014ae72456552aa4e4a7eb29848c2a1e553caa7854f1a8e251c5c34b31032313330b2b1b3b072717370f2f1fbf80a090b088a898b884a494b48cac9cbc82a292b28aaa9aba86a696b68eae9ebe81a191b189a999b985a595b58dad9dbd83a393b38bab9bbb87a797b78faf9f7f4060507048685878446454744c6c5c7c426252724a6a5a7a466656764e6e5e7e4161517149695979456555754d6d5d7d436353734b6b5b7b476757774f6f5fff848993264f993a6dfa8c99b366cf993b6ffe82858b162f59ba6cf98a95ab56af59bb6efd868d9b366fd9ba6dfb8e9dbb76efd9bb6fff8183870e1f397aecf88993a74e9f397beefc858b972e5fb97aedfa8d9bb76edfb97beffe83878f1e3f79faecf98b97af5ebf79fbeefd878f9f3e7ff9faedfb8f9fbf7efff9fbef3f0073e905c6";

fn sample_data() -> Vec<u8> {
    let mut data = b"The quick brown fox jumps over the lazy dog. ".repeat(40);
    data.extend(0u8..=255);
    data
}

fn decode_hex(line: &str) -> Vec<u8> {
    (0..line.len() / 2)
        .map(|index| u8::from_str_radix(&line[index * 2..index * 2 + 2], 16).expect("valid hex digit pair"))
        .collect()
}

fn inflate_all(compressed: &[u8], chunk: usize) -> Vec<u8> {
    let mut decompressor = Decompress::new();
    let mut output = Vec::new();
    let mut buffer = vec![0u8; 64];
    for piece in compressed.chunks(chunk) {
        if decompressor.is_finished() {
            break;
        }
        decompressor.input(piece);
        loop {
            let avail = decompressor.inflate(&mut buffer).expect("inflate") as usize;
            output.extend_from_slice(&buffer[..buffer.len() - avail]);
            if avail != 0 {
                break;
            }
        }
    }
    assert!(decompressor.is_finished());
    output
}

#[test]
fn decompress_zlib_stream() {
    let compressed = decode_hex(ZLIB_STREAM);
    for chunk in [1, 7, 100, compressed.len()] {
        assert_eq!(inflate_all(&compressed, chunk), sample_data());
    }
}

#[test]
fn decompress_corrupt_stream() {
    let mut decompressor = Decompress::new();
    decompressor.input(&[0x78, 0x9c, 0xff, 0xff, 0xff, 0xff]);
    let mut buffer = vec![0u8; 64];
    let err = decompressor.inflate(&mut buffer).expect_err("corrupt data is rejected");
    assert_eq!(err.explain(), "Error decompressing stream");
}

#[test]
fn compress_round_trip() {
    let data = sample_data();
    let mut compressor = Compress::new(9).expect("compressor");
    compressor.input(&data);
    let mut compressed = Vec::new();
    let mut buffer = vec![0u8; 32];
    loop {
        let avail = compressor.deflate(&mut buffer, true).expect("deflate") as usize;
        compressed.extend_from_slice(&buffer[..buffer.len() - avail]);
        if avail != 0 {
            break;
        }
    }
    assert_eq!(inflate_all(&compressed, 13), data);
}

#[test]
fn compress_buffer_round_trip() {
    let data: Vec<u8> = (0..20000u32).map(|value| (value * 7 % 251) as u8).collect();
    let mut stream = CompressBuffer::new(Vec::new(), 6).expect("compress buffer");
    stream.write_bytes(&data).expect("write");
    stream.sync().expect("sync");
    let compressed = stream.into_inner();
    assert_eq!(inflate_all(&compressed, 4096), data);
}

#[test]
fn compress_rejects_bad_level() {
    assert!(Compress::new(10).is_err());
}

fn format_decode_style(compressed: &[u8]) -> Vec<u8> {
    let mut decompressor = Decompress::new();
    let mut chunks: Vec<Vec<u8>> = Vec::new();
    let mut out_avail = 0usize;
    for piece in compressed.chunks(4096) {
        if decompressor.is_finished() {
            break;
        }
        decompressor.input(piece);
        loop {
            if out_avail == 0 {
                chunks.push(vec![0u8; 1024]);
                out_avail = 1024;
            }
            let buffer = chunks.last_mut().expect("output chunk");
            let start = 1024 - out_avail;
            out_avail = decompressor.inflate(&mut buffer[start..]).expect("inflate") as usize;
            if out_avail != 0 {
                break;
            }
        }
    }
    if let Some(last) = chunks.last_mut() {
        last.truncate(1024 - out_avail);
    }
    chunks.concat()
}

#[test]
fn decompress_fills_output_like_zlib() {
    let mut data = Vec::new();
    let mut state: u32 = 12345;
    for index in 0..300000u32 {
        state = state.wrapping_mul(1103515245).wrapping_add(12345);
        let byte = if index % 3 != 0 {
            (state >> 16) as u8
        } else {
            (index / 13 % 251) as u8
        };
        data.push(byte);
    }
    let mut compressor = Compress::new(6).expect("compressor");
    compressor.input(&data);
    let mut compressed = Vec::new();
    let mut buffer = vec![0u8; 4096];
    loop {
        let avail = compressor.deflate(&mut buffer, true).expect("deflate") as usize;
        compressed.extend_from_slice(&buffer[..buffer.len() - avail]);
        if avail != 0 {
            break;
        }
    }
    assert_eq!(format_decode_style(&compressed), data);
}

#[test]
fn decompress_sla_file_like_format_decode() {
    let path = format!("{}/tests/core_data/avr8eind.sla", env!("CARGO_MANIFEST_DIR"));
    let data = std::fs::read(path).expect("sla test file");
    assert_eq!(&data[..4], b"sla\x04");
    for output in [format_decode_style(&data[4..]), inflate_all(&data[4..], 4096)] {
        let mut crc: u32 = !0;
        for byte in &output {
            crc = ghidra_decompiler::crc32::crc_update(crc, *byte as u32);
        }
        assert_eq!(output.len(), 84708);
        assert_eq!(!crc, 0x6dd1b279);
    }
}

#[test]
fn xz_sla_payload() {
    let path = format!("{}/tests/core_data/avr8eind.sla", env!("CARGO_MANIFEST_DIR"));
    let zlib_image = std::fs::read(path).expect("missing sla test file");
    let payload = decompress_sla(&zlib_image)
        .expect("invalid zlib payload")
        .expect("empty payload");
    let mut xz_image = zlib_image[..4].to_vec();
    lzma_rs::xz_compress(&mut payload.as_slice(), &mut xz_image).expect("xz compression failure");
    assert_eq!(
        decompress_sla(&xz_image).expect("invalid xz payload"),
        Some(payload),
        "embedded .sla files contain xz payloads to fit the crates.io size limit; they must decode to the zlib payload"
    );
}
