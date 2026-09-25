pub struct EmbeddedFile {
    pub processor: &'static str,
    pub path: &'static str,
    pub data: &'static [u8],
}

pub static EMBEDDED_PROCESSORS: &[(&str, bool)] = &[
    ("6502", cfg!(feature = "6502")),
    ("68000", cfg!(feature = "68000")),
    ("8048", cfg!(feature = "8048")),
    ("8051", cfg!(feature = "8051")),
    ("8085", cfg!(feature = "8085")),
    ("AARCH64", cfg!(feature = "aarch64")),
    ("ARM", cfg!(feature = "arm")),
    ("Atmel", cfg!(feature = "atmel")),
    ("BPF", cfg!(feature = "bpf")),
    ("CP1600", cfg!(feature = "cp1600")),
    ("CR16", cfg!(feature = "cr16")),
    ("Dalvik", cfg!(feature = "dalvik")),
    ("DATA", cfg!(feature = "data")),
    ("eBPF", cfg!(feature = "ebpf")),
    ("HCS08", cfg!(feature = "hcs08")),
    ("HCS12", cfg!(feature = "hcs12")),
    ("Hexagon", cfg!(feature = "hexagon")),
    ("JVM", cfg!(feature = "jvm")),
    ("Loongarch", cfg!(feature = "loongarch")),
    ("M16C", cfg!(feature = "m16c")),
    ("M8C", cfg!(feature = "m8c")),
    ("MC6800", cfg!(feature = "mc6800")),
    ("MCS96", cfg!(feature = "mcs96")),
    ("MIPS", cfg!(feature = "mips")),
    ("NDS32", cfg!(feature = "nds32")),
    ("PA-RISC", cfg!(feature = "pa-risc")),
    ("PIC", cfg!(feature = "pic")),
    ("PowerPC", cfg!(feature = "powerpc")),
    ("RISCV", cfg!(feature = "riscv")),
    ("Sparc", cfg!(feature = "sparc")),
    ("SuperH", cfg!(feature = "superh")),
    ("SuperH4", cfg!(feature = "superh4")),
    ("TI_MSP430", cfg!(feature = "ti_msp430")),
    ("Toy", cfg!(feature = "toy")),
    ("tricore", cfg!(feature = "tricore")),
    ("V850", cfg!(feature = "v850")),
    ("x86", cfg!(feature = "x86")),
    ("Xtensa", cfg!(feature = "xtensa")),
    ("Z80", cfg!(feature = "z80")),
];

pub static EMBEDDED_FILES: &[EmbeddedFile] = &[
    #[cfg(feature = "6502")]
    EmbeddedFile {
        processor: "6502",
        path: "6502.cspec",
        data: include_bytes!("../languages/6502/6502.cspec"),
    },
    #[cfg(feature = "6502")]
    EmbeddedFile {
        processor: "6502",
        path: "6502.ldefs",
        data: include_bytes!("../languages/6502/6502.ldefs"),
    },
    #[cfg(feature = "6502")]
    EmbeddedFile {
        processor: "6502",
        path: "6502.pspec",
        data: include_bytes!("../languages/6502/6502.pspec"),
    },
    #[cfg(feature = "6502")]
    EmbeddedFile {
        processor: "6502",
        path: "6502.sla",
        data: include_bytes!("../languages/6502/6502.sla"),
    },
    #[cfg(feature = "6502")]
    EmbeddedFile {
        processor: "6502",
        path: "65c02.sla",
        data: include_bytes!("../languages/6502/65c02.sla"),
    },
    #[cfg(feature = "68000")]
    EmbeddedFile {
        processor: "68000",
        path: "68000.cspec",
        data: include_bytes!("../languages/68000/68000.cspec"),
    },
    #[cfg(feature = "68000")]
    EmbeddedFile {
        processor: "68000",
        path: "68000.ldefs",
        data: include_bytes!("../languages/68000/68000.ldefs"),
    },
    #[cfg(feature = "68000")]
    EmbeddedFile {
        processor: "68000",
        path: "68000.pspec",
        data: include_bytes!("../languages/68000/68000.pspec"),
    },
    #[cfg(feature = "68000")]
    EmbeddedFile {
        processor: "68000",
        path: "68000_register.cspec",
        data: include_bytes!("../languages/68000/68000_register.cspec"),
    },
    #[cfg(feature = "68000")]
    EmbeddedFile {
        processor: "68000",
        path: "68020.sla",
        data: include_bytes!("../languages/68000/68020.sla"),
    },
    #[cfg(feature = "68000")]
    EmbeddedFile {
        processor: "68000",
        path: "68030.sla",
        data: include_bytes!("../languages/68000/68030.sla"),
    },
    #[cfg(feature = "68000")]
    EmbeddedFile {
        processor: "68000",
        path: "68040.sla",
        data: include_bytes!("../languages/68000/68040.sla"),
    },
    #[cfg(feature = "68000")]
    EmbeddedFile {
        processor: "68000",
        path: "CPU32.sla",
        data: include_bytes!("../languages/68000/CPU32.sla"),
    },
    #[cfg(feature = "68000")]
    EmbeddedFile {
        processor: "68000",
        path: "coldfire.sla",
        data: include_bytes!("../languages/68000/coldfire.sla"),
    },
    #[cfg(feature = "8048")]
    EmbeddedFile {
        processor: "8048",
        path: "8048.cspec",
        data: include_bytes!("../languages/8048/8048.cspec"),
    },
    #[cfg(feature = "8048")]
    EmbeddedFile {
        processor: "8048",
        path: "8048.ldefs",
        data: include_bytes!("../languages/8048/8048.ldefs"),
    },
    #[cfg(feature = "8048")]
    EmbeddedFile {
        processor: "8048",
        path: "8048.pspec",
        data: include_bytes!("../languages/8048/8048.pspec"),
    },
    #[cfg(feature = "8048")]
    EmbeddedFile {
        processor: "8048",
        path: "8048.sla",
        data: include_bytes!("../languages/8048/8048.sla"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "80251.cspec",
        data: include_bytes!("../languages/8051/80251.cspec"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "80251.pspec",
        data: include_bytes!("../languages/8051/80251.pspec"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "80251.sla",
        data: include_bytes!("../languages/8051/80251.sla"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "80390.cspec",
        data: include_bytes!("../languages/8051/80390.cspec"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "80390.sla",
        data: include_bytes!("../languages/8051/80390.sla"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "8051.cspec",
        data: include_bytes!("../languages/8051/8051.cspec"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "8051.ldefs",
        data: include_bytes!("../languages/8051/8051.ldefs"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "8051.pspec",
        data: include_bytes!("../languages/8051/8051.pspec"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "8051.sla",
        data: include_bytes!("../languages/8051/8051.sla"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "8051_archimedes.cspec",
        data: include_bytes!("../languages/8051/8051_archimedes.cspec"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "cip-51.pspec",
        data: include_bytes!("../languages/8051/cip-51.pspec"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "cip-51.sla",
        data: include_bytes!("../languages/8051/cip-51.sla"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "keil-cx51.cspec",
        data: include_bytes!("../languages/8051/keil-cx51.cspec"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "mx51.cspec",
        data: include_bytes!("../languages/8051/mx51.cspec"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "mx51.pspec",
        data: include_bytes!("../languages/8051/mx51.pspec"),
    },
    #[cfg(feature = "8051")]
    EmbeddedFile {
        processor: "8051",
        path: "mx51.sla",
        data: include_bytes!("../languages/8051/mx51.sla"),
    },
    #[cfg(feature = "8085")]
    EmbeddedFile {
        processor: "8085",
        path: "8085.cspec",
        data: include_bytes!("../languages/8085/8085.cspec"),
    },
    #[cfg(feature = "8085")]
    EmbeddedFile {
        processor: "8085",
        path: "8085.ldefs",
        data: include_bytes!("../languages/8085/8085.ldefs"),
    },
    #[cfg(feature = "8085")]
    EmbeddedFile {
        processor: "8085",
        path: "8085.pspec",
        data: include_bytes!("../languages/8085/8085.pspec"),
    },
    #[cfg(feature = "8085")]
    EmbeddedFile {
        processor: "8085",
        path: "8085.sla",
        data: include_bytes!("../languages/8085/8085.sla"),
    },
    #[cfg(feature = "aarch64")]
    EmbeddedFile {
        processor: "AARCH64",
        path: "AARCH64.cspec",
        data: include_bytes!("../languages/AARCH64/AARCH64.cspec"),
    },
    #[cfg(feature = "aarch64")]
    EmbeddedFile {
        processor: "AARCH64",
        path: "AARCH64.ldefs",
        data: include_bytes!("../languages/AARCH64/AARCH64.ldefs"),
    },
    #[cfg(feature = "aarch64")]
    EmbeddedFile {
        processor: "AARCH64",
        path: "AARCH64.pspec",
        data: include_bytes!("../languages/AARCH64/AARCH64.pspec"),
    },
    #[cfg(feature = "aarch64")]
    EmbeddedFile {
        processor: "AARCH64",
        path: "AARCH64.sla",
        data: include_bytes!("../languages/AARCH64/AARCH64.sla"),
    },
    #[cfg(feature = "aarch64")]
    EmbeddedFile {
        processor: "AARCH64",
        path: "AARCH64BE.sla",
        data: include_bytes!("../languages/AARCH64/AARCH64BE.sla"),
    },
    #[cfg(feature = "aarch64")]
    EmbeddedFile {
        processor: "AARCH64",
        path: "AARCH64_AppleSilicon.sla",
        data: include_bytes!("../languages/AARCH64/AARCH64_AppleSilicon.sla"),
    },
    #[cfg(feature = "aarch64")]
    EmbeddedFile {
        processor: "AARCH64",
        path: "AARCH64_apple.cspec",
        data: include_bytes!("../languages/AARCH64/AARCH64_apple.cspec"),
    },
    #[cfg(feature = "aarch64")]
    EmbeddedFile {
        processor: "AARCH64",
        path: "AARCH64_golang.cspec",
        data: include_bytes!("../languages/AARCH64/AARCH64_golang.cspec"),
    },
    #[cfg(feature = "aarch64")]
    EmbeddedFile {
        processor: "AARCH64",
        path: "AARCH64_ilp32.cspec",
        data: include_bytes!("../languages/AARCH64/AARCH64_ilp32.cspec"),
    },
    #[cfg(feature = "aarch64")]
    EmbeddedFile {
        processor: "AARCH64",
        path: "AARCH64_win.cspec",
        data: include_bytes!("../languages/AARCH64/AARCH64_win.cspec"),
    },
    #[cfg(feature = "aarch64")]
    EmbeddedFile {
        processor: "AARCH64",
        path: "AppleSilicon.ldefs",
        data: include_bytes!("../languages/AARCH64/AppleSilicon.ldefs"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM.cspec",
        data: include_bytes!("../languages/ARM/ARM.cspec"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM.ldefs",
        data: include_bytes!("../languages/ARM/ARM.ldefs"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM4_be.sla",
        data: include_bytes!("../languages/ARM/ARM4_be.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM4_le.sla",
        data: include_bytes!("../languages/ARM/ARM4_le.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM4t_be.sla",
        data: include_bytes!("../languages/ARM/ARM4t_be.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM4t_le.sla",
        data: include_bytes!("../languages/ARM/ARM4t_le.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM5_be.sla",
        data: include_bytes!("../languages/ARM/ARM5_be.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM5_le.sla",
        data: include_bytes!("../languages/ARM/ARM5_le.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM5t_be.sla",
        data: include_bytes!("../languages/ARM/ARM5t_be.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM5t_le.sla",
        data: include_bytes!("../languages/ARM/ARM5t_le.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM6_be.sla",
        data: include_bytes!("../languages/ARM/ARM6_be.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM6_le.sla",
        data: include_bytes!("../languages/ARM/ARM6_le.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM7_be.sla",
        data: include_bytes!("../languages/ARM/ARM7_be.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM7_le.sla",
        data: include_bytes!("../languages/ARM/ARM7_le.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM8_be.sla",
        data: include_bytes!("../languages/ARM/ARM8_be.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM8_le.sla",
        data: include_bytes!("../languages/ARM/ARM8_le.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM8m_be.sla",
        data: include_bytes!("../languages/ARM/ARM8m_be.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM8m_le.sla",
        data: include_bytes!("../languages/ARM/ARM8m_le.sla"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARMCortex.pspec",
        data: include_bytes!("../languages/ARM/ARMCortex.pspec"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM_apcs.cspec",
        data: include_bytes!("../languages/ARM/ARM_apcs.cspec"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM_v45.cspec",
        data: include_bytes!("../languages/ARM/ARM_v45.cspec"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM_v45.pspec",
        data: include_bytes!("../languages/ARM/ARM_v45.pspec"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARM_win.cspec",
        data: include_bytes!("../languages/ARM/ARM_win.cspec"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARMt.pspec",
        data: include_bytes!("../languages/ARM/ARMt.pspec"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARMtTHUMB.pspec",
        data: include_bytes!("../languages/ARM/ARMtTHUMB.pspec"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARMt_v45.pspec",
        data: include_bytes!("../languages/ARM/ARMt_v45.pspec"),
    },
    #[cfg(feature = "arm")]
    EmbeddedFile {
        processor: "ARM",
        path: "ARMt_v6.pspec",
        data: include_bytes!("../languages/ARM/ARMt_v6.pspec"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "atmega256.pspec",
        data: include_bytes!("../languages/Atmel/atmega256.pspec"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr32a.cspec",
        data: include_bytes!("../languages/Atmel/avr32a.cspec"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr32a.ldefs",
        data: include_bytes!("../languages/Atmel/avr32a.ldefs"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr32a.pspec",
        data: include_bytes!("../languages/Atmel/avr32a.pspec"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr32a.sla",
        data: include_bytes!("../languages/Atmel/avr32a.sla"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr8.ldefs",
        data: include_bytes!("../languages/Atmel/avr8.ldefs"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr8.pspec",
        data: include_bytes!("../languages/Atmel/avr8.pspec"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr8.sla",
        data: include_bytes!("../languages/Atmel/avr8.sla"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr8e.sla",
        data: include_bytes!("../languages/Atmel/avr8e.sla"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr8egcc.cspec",
        data: include_bytes!("../languages/Atmel/avr8egcc.cspec"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr8eind.sla",
        data: include_bytes!("../languages/Atmel/avr8eind.sla"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr8gcc.cspec",
        data: include_bytes!("../languages/Atmel/avr8gcc.cspec"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr8iarV1.cspec",
        data: include_bytes!("../languages/Atmel/avr8iarV1.cspec"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr8imgCraftV8.cspec",
        data: include_bytes!("../languages/Atmel/avr8imgCraftV8.cspec"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr8xmega.pspec",
        data: include_bytes!("../languages/Atmel/avr8xmega.pspec"),
    },
    #[cfg(feature = "atmel")]
    EmbeddedFile {
        processor: "Atmel",
        path: "avr8xmega.sla",
        data: include_bytes!("../languages/Atmel/avr8xmega.sla"),
    },
    #[cfg(feature = "bpf")]
    EmbeddedFile {
        processor: "BPF",
        path: "BPF.cspec",
        data: include_bytes!("../languages/BPF/BPF.cspec"),
    },
    #[cfg(feature = "bpf")]
    EmbeddedFile {
        processor: "BPF",
        path: "BPF.ldefs",
        data: include_bytes!("../languages/BPF/BPF.ldefs"),
    },
    #[cfg(feature = "bpf")]
    EmbeddedFile {
        processor: "BPF",
        path: "BPF.pspec",
        data: include_bytes!("../languages/BPF/BPF.pspec"),
    },
    #[cfg(feature = "bpf")]
    EmbeddedFile {
        processor: "BPF",
        path: "BPF_le.sla",
        data: include_bytes!("../languages/BPF/BPF_le.sla"),
    },
    #[cfg(feature = "cp1600")]
    EmbeddedFile {
        processor: "CP1600",
        path: "CP1600.cspec",
        data: include_bytes!("../languages/CP1600/CP1600.cspec"),
    },
    #[cfg(feature = "cp1600")]
    EmbeddedFile {
        processor: "CP1600",
        path: "CP1600.ldefs",
        data: include_bytes!("../languages/CP1600/CP1600.ldefs"),
    },
    #[cfg(feature = "cp1600")]
    EmbeddedFile {
        processor: "CP1600",
        path: "CP1600.pspec",
        data: include_bytes!("../languages/CP1600/CP1600.pspec"),
    },
    #[cfg(feature = "cp1600")]
    EmbeddedFile {
        processor: "CP1600",
        path: "CP1600.sla",
        data: include_bytes!("../languages/CP1600/CP1600.sla"),
    },
    #[cfg(feature = "cr16")]
    EmbeddedFile {
        processor: "CR16",
        path: "CR16.cspec",
        data: include_bytes!("../languages/CR16/CR16.cspec"),
    },
    #[cfg(feature = "cr16")]
    EmbeddedFile {
        processor: "CR16",
        path: "CR16.ldefs",
        data: include_bytes!("../languages/CR16/CR16.ldefs"),
    },
    #[cfg(feature = "cr16")]
    EmbeddedFile {
        processor: "CR16",
        path: "CR16.pspec",
        data: include_bytes!("../languages/CR16/CR16.pspec"),
    },
    #[cfg(feature = "cr16")]
    EmbeddedFile {
        processor: "CR16",
        path: "CR16B.sla",
        data: include_bytes!("../languages/CR16/CR16B.sla"),
    },
    #[cfg(feature = "cr16")]
    EmbeddedFile {
        processor: "CR16",
        path: "CR16C.sla",
        data: include_bytes!("../languages/CR16/CR16C.sla"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik.ldefs",
        data: include_bytes!("../languages/Dalvik/Dalvik.ldefs"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_Base.cspec",
        data: include_bytes!("../languages/Dalvik/Dalvik_Base.cspec"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_Base.pspec",
        data: include_bytes!("../languages/Dalvik/Dalvik_Base.pspec"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_Base.sla",
        data: include_bytes!("../languages/Dalvik/Dalvik_Base.sla"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_DEX_Android10.sla",
        data: include_bytes!("../languages/Dalvik/Dalvik_DEX_Android10.sla"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_DEX_Android11.sla",
        data: include_bytes!("../languages/Dalvik/Dalvik_DEX_Android11.sla"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_DEX_Android12.sla",
        data: include_bytes!("../languages/Dalvik/Dalvik_DEX_Android12.sla"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_DEX_KitKat.sla",
        data: include_bytes!("../languages/Dalvik/Dalvik_DEX_KitKat.sla"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_DEX_Lollipop.sla",
        data: include_bytes!("../languages/Dalvik/Dalvik_DEX_Lollipop.sla"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_DEX_Marshmallow.sla",
        data: include_bytes!("../languages/Dalvik/Dalvik_DEX_Marshmallow.sla"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_DEX_Nougat.sla",
        data: include_bytes!("../languages/Dalvik/Dalvik_DEX_Nougat.sla"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_DEX_Oreo.sla",
        data: include_bytes!("../languages/Dalvik/Dalvik_DEX_Oreo.sla"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_DEX_Pie.sla",
        data: include_bytes!("../languages/Dalvik/Dalvik_DEX_Pie.sla"),
    },
    #[cfg(feature = "dalvik")]
    EmbeddedFile {
        processor: "Dalvik",
        path: "Dalvik_ODEX_KitKat.sla",
        data: include_bytes!("../languages/Dalvik/Dalvik_ODEX_KitKat.sla"),
    },
    #[cfg(feature = "data")]
    EmbeddedFile {
        processor: "DATA",
        path: "data-be-64.sla",
        data: include_bytes!("../languages/DATA/data-be-64.sla"),
    },
    #[cfg(feature = "data")]
    EmbeddedFile {
        processor: "DATA",
        path: "data-le-64.sla",
        data: include_bytes!("../languages/DATA/data-le-64.sla"),
    },
    #[cfg(feature = "data")]
    EmbeddedFile {
        processor: "DATA",
        path: "data-ptr16.cspec",
        data: include_bytes!("../languages/DATA/data-ptr16.cspec"),
    },
    #[cfg(feature = "data")]
    EmbeddedFile {
        processor: "DATA",
        path: "data-ptr32.cspec",
        data: include_bytes!("../languages/DATA/data-ptr32.cspec"),
    },
    #[cfg(feature = "data")]
    EmbeddedFile {
        processor: "DATA",
        path: "data-ptr64.cspec",
        data: include_bytes!("../languages/DATA/data-ptr64.cspec"),
    },
    #[cfg(feature = "data")]
    EmbeddedFile {
        processor: "DATA",
        path: "data.ldefs",
        data: include_bytes!("../languages/DATA/data.ldefs"),
    },
    #[cfg(feature = "data")]
    EmbeddedFile {
        processor: "DATA",
        path: "data.pspec",
        data: include_bytes!("../languages/DATA/data.pspec"),
    },
    #[cfg(feature = "ebpf")]
    EmbeddedFile {
        processor: "eBPF",
        path: "eBPF.cspec",
        data: include_bytes!("../languages/eBPF/eBPF.cspec"),
    },
    #[cfg(feature = "ebpf")]
    EmbeddedFile {
        processor: "eBPF",
        path: "eBPF.ldefs",
        data: include_bytes!("../languages/eBPF/eBPF.ldefs"),
    },
    #[cfg(feature = "ebpf")]
    EmbeddedFile {
        processor: "eBPF",
        path: "eBPF.pspec",
        data: include_bytes!("../languages/eBPF/eBPF.pspec"),
    },
    #[cfg(feature = "ebpf")]
    EmbeddedFile {
        processor: "eBPF",
        path: "eBPF_be.sla",
        data: include_bytes!("../languages/eBPF/eBPF_be.sla"),
    },
    #[cfg(feature = "ebpf")]
    EmbeddedFile {
        processor: "eBPF",
        path: "eBPF_le.sla",
        data: include_bytes!("../languages/eBPF/eBPF_le.sla"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HC05-M68HC05TB.pspec",
        data: include_bytes!("../languages/HCS08/HC05-M68HC05TB.pspec"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HC05.cspec",
        data: include_bytes!("../languages/HCS08/HC05.cspec"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HC05.ldefs",
        data: include_bytes!("../languages/HCS08/HC05.ldefs"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HC05.pspec",
        data: include_bytes!("../languages/HCS08/HC05.pspec"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HC05.sla",
        data: include_bytes!("../languages/HCS08/HC05.sla"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HC08-MC68HC908QY4.pspec",
        data: include_bytes!("../languages/HCS08/HC08-MC68HC908QY4.pspec"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HC08.ldefs",
        data: include_bytes!("../languages/HCS08/HC08.ldefs"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HC08.pspec",
        data: include_bytes!("../languages/HCS08/HC08.pspec"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HC08.sla",
        data: include_bytes!("../languages/HCS08/HC08.sla"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HCS08-MC9S08GB60.pspec",
        data: include_bytes!("../languages/HCS08/HCS08-MC9S08GB60.pspec"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HCS08.cspec",
        data: include_bytes!("../languages/HCS08/HCS08.cspec"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HCS08.ldefs",
        data: include_bytes!("../languages/HCS08/HCS08.ldefs"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HCS08.pspec",
        data: include_bytes!("../languages/HCS08/HCS08.pspec"),
    },
    #[cfg(feature = "hcs08")]
    EmbeddedFile {
        processor: "HCS08",
        path: "HCS08.sla",
        data: include_bytes!("../languages/HCS08/HCS08.sla"),
    },
    #[cfg(feature = "hcs12")]
    EmbeddedFile {
        processor: "HCS12",
        path: "HC12.cspec",
        data: include_bytes!("../languages/HCS12/HC12.cspec"),
    },
    #[cfg(feature = "hcs12")]
    EmbeddedFile {
        processor: "HCS12",
        path: "HC12.pspec",
        data: include_bytes!("../languages/HCS12/HC12.pspec"),
    },
    #[cfg(feature = "hcs12")]
    EmbeddedFile {
        processor: "HCS12",
        path: "HC12.sla",
        data: include_bytes!("../languages/HCS12/HC12.sla"),
    },
    #[cfg(feature = "hcs12")]
    EmbeddedFile {
        processor: "HCS12",
        path: "HCS12.cspec",
        data: include_bytes!("../languages/HCS12/HCS12.cspec"),
    },
    #[cfg(feature = "hcs12")]
    EmbeddedFile {
        processor: "HCS12",
        path: "HCS12.ldefs",
        data: include_bytes!("../languages/HCS12/HCS12.ldefs"),
    },
    #[cfg(feature = "hcs12")]
    EmbeddedFile {
        processor: "HCS12",
        path: "HCS12.pspec",
        data: include_bytes!("../languages/HCS12/HCS12.pspec"),
    },
    #[cfg(feature = "hcs12")]
    EmbeddedFile {
        processor: "HCS12",
        path: "HCS12.sla",
        data: include_bytes!("../languages/HCS12/HCS12.sla"),
    },
    #[cfg(feature = "hcs12")]
    EmbeddedFile {
        processor: "HCS12",
        path: "HCS12X.cspec",
        data: include_bytes!("../languages/HCS12/HCS12X.cspec"),
    },
    #[cfg(feature = "hcs12")]
    EmbeddedFile {
        processor: "HCS12",
        path: "HCS12X.pspec",
        data: include_bytes!("../languages/HCS12/HCS12X.pspec"),
    },
    #[cfg(feature = "hcs12")]
    EmbeddedFile {
        processor: "HCS12",
        path: "HCS12X.sla",
        data: include_bytes!("../languages/HCS12/HCS12X.sla"),
    },
    #[cfg(feature = "hexagon")]
    EmbeddedFile {
        processor: "Hexagon",
        path: "hexagon.cspec",
        data: include_bytes!("../languages/Hexagon/hexagon.cspec"),
    },
    #[cfg(feature = "hexagon")]
    EmbeddedFile {
        processor: "Hexagon",
        path: "hexagon.ldefs",
        data: include_bytes!("../languages/Hexagon/hexagon.ldefs"),
    },
    #[cfg(feature = "hexagon")]
    EmbeddedFile {
        processor: "Hexagon",
        path: "hexagon.pspec",
        data: include_bytes!("../languages/Hexagon/hexagon.pspec"),
    },
    #[cfg(feature = "hexagon")]
    EmbeddedFile {
        processor: "Hexagon",
        path: "hexagon.sla",
        data: include_bytes!("../languages/Hexagon/hexagon.sla"),
    },
    #[cfg(feature = "jvm")]
    EmbeddedFile {
        processor: "JVM",
        path: "JVM.cspec",
        data: include_bytes!("../languages/JVM/JVM.cspec"),
    },
    #[cfg(feature = "jvm")]
    EmbeddedFile {
        processor: "JVM",
        path: "JVM.ldefs",
        data: include_bytes!("../languages/JVM/JVM.ldefs"),
    },
    #[cfg(feature = "jvm")]
    EmbeddedFile {
        processor: "JVM",
        path: "JVM.pspec",
        data: include_bytes!("../languages/JVM/JVM.pspec"),
    },
    #[cfg(feature = "jvm")]
    EmbeddedFile {
        processor: "JVM",
        path: "JVM.sla",
        data: include_bytes!("../languages/JVM/JVM.sla"),
    },
    #[cfg(feature = "loongarch")]
    EmbeddedFile {
        processor: "Loongarch",
        path: "ilp32d.cspec",
        data: include_bytes!("../languages/Loongarch/ilp32d.cspec"),
    },
    #[cfg(feature = "loongarch")]
    EmbeddedFile {
        processor: "Loongarch",
        path: "ilp32f.cspec",
        data: include_bytes!("../languages/Loongarch/ilp32f.cspec"),
    },
    #[cfg(feature = "loongarch")]
    EmbeddedFile {
        processor: "Loongarch",
        path: "loongarch.ldefs",
        data: include_bytes!("../languages/Loongarch/loongarch.ldefs"),
    },
    #[cfg(feature = "loongarch")]
    EmbeddedFile {
        processor: "Loongarch",
        path: "loongarch32.pspec",
        data: include_bytes!("../languages/Loongarch/loongarch32.pspec"),
    },
    #[cfg(feature = "loongarch")]
    EmbeddedFile {
        processor: "Loongarch",
        path: "loongarch32_f32.sla",
        data: include_bytes!("../languages/Loongarch/loongarch32_f32.sla"),
    },
    #[cfg(feature = "loongarch")]
    EmbeddedFile {
        processor: "Loongarch",
        path: "loongarch32_f64.sla",
        data: include_bytes!("../languages/Loongarch/loongarch32_f64.sla"),
    },
    #[cfg(feature = "loongarch")]
    EmbeddedFile {
        processor: "Loongarch",
        path: "loongarch64.pspec",
        data: include_bytes!("../languages/Loongarch/loongarch64.pspec"),
    },
    #[cfg(feature = "loongarch")]
    EmbeddedFile {
        processor: "Loongarch",
        path: "loongarch64_f32.sla",
        data: include_bytes!("../languages/Loongarch/loongarch64_f32.sla"),
    },
    #[cfg(feature = "loongarch")]
    EmbeddedFile {
        processor: "Loongarch",
        path: "loongarch64_f64.sla",
        data: include_bytes!("../languages/Loongarch/loongarch64_f64.sla"),
    },
    #[cfg(feature = "loongarch")]
    EmbeddedFile {
        processor: "Loongarch",
        path: "lp64d.cspec",
        data: include_bytes!("../languages/Loongarch/lp64d.cspec"),
    },
    #[cfg(feature = "loongarch")]
    EmbeddedFile {
        processor: "Loongarch",
        path: "lp64f.cspec",
        data: include_bytes!("../languages/Loongarch/lp64f.cspec"),
    },
    #[cfg(feature = "m16c")]
    EmbeddedFile {
        processor: "M16C",
        path: "M16C_60.cspec",
        data: include_bytes!("../languages/M16C/M16C_60.cspec"),
    },
    #[cfg(feature = "m16c")]
    EmbeddedFile {
        processor: "M16C",
        path: "M16C_60.ldefs",
        data: include_bytes!("../languages/M16C/M16C_60.ldefs"),
    },
    #[cfg(feature = "m16c")]
    EmbeddedFile {
        processor: "M16C",
        path: "M16C_60.pspec",
        data: include_bytes!("../languages/M16C/M16C_60.pspec"),
    },
    #[cfg(feature = "m16c")]
    EmbeddedFile {
        processor: "M16C",
        path: "M16C_60.sla",
        data: include_bytes!("../languages/M16C/M16C_60.sla"),
    },
    #[cfg(feature = "m16c")]
    EmbeddedFile {
        processor: "M16C",
        path: "M16C_80.cspec",
        data: include_bytes!("../languages/M16C/M16C_80.cspec"),
    },
    #[cfg(feature = "m16c")]
    EmbeddedFile {
        processor: "M16C",
        path: "M16C_80.ldefs",
        data: include_bytes!("../languages/M16C/M16C_80.ldefs"),
    },
    #[cfg(feature = "m16c")]
    EmbeddedFile {
        processor: "M16C",
        path: "M16C_80.pspec",
        data: include_bytes!("../languages/M16C/M16C_80.pspec"),
    },
    #[cfg(feature = "m16c")]
    EmbeddedFile {
        processor: "M16C",
        path: "M16C_80.sla",
        data: include_bytes!("../languages/M16C/M16C_80.sla"),
    },
    #[cfg(feature = "m8c")]
    EmbeddedFile {
        processor: "M8C",
        path: "m8c.cspec",
        data: include_bytes!("../languages/M8C/m8c.cspec"),
    },
    #[cfg(feature = "m8c")]
    EmbeddedFile {
        processor: "M8C",
        path: "m8c.ldefs",
        data: include_bytes!("../languages/M8C/m8c.ldefs"),
    },
    #[cfg(feature = "m8c")]
    EmbeddedFile {
        processor: "M8C",
        path: "m8c.pspec",
        data: include_bytes!("../languages/M8C/m8c.pspec"),
    },
    #[cfg(feature = "m8c")]
    EmbeddedFile {
        processor: "M8C",
        path: "m8c.sla",
        data: include_bytes!("../languages/M8C/m8c.sla"),
    },
    #[cfg(feature = "mc6800")]
    EmbeddedFile {
        processor: "MC6800",
        path: "6800.ldefs",
        data: include_bytes!("../languages/MC6800/6800.ldefs"),
    },
    #[cfg(feature = "mc6800")]
    EmbeddedFile {
        processor: "MC6800",
        path: "6805.cspec",
        data: include_bytes!("../languages/MC6800/6805.cspec"),
    },
    #[cfg(feature = "mc6800")]
    EmbeddedFile {
        processor: "MC6800",
        path: "6805.ldefs",
        data: include_bytes!("../languages/MC6800/6805.ldefs"),
    },
    #[cfg(feature = "mc6800")]
    EmbeddedFile {
        processor: "MC6800",
        path: "6805.pspec",
        data: include_bytes!("../languages/MC6800/6805.pspec"),
    },
    #[cfg(feature = "mc6800")]
    EmbeddedFile {
        processor: "MC6800",
        path: "6805.sla",
        data: include_bytes!("../languages/MC6800/6805.sla"),
    },
    #[cfg(feature = "mc6800")]
    EmbeddedFile {
        processor: "MC6800",
        path: "6809.cspec",
        data: include_bytes!("../languages/MC6800/6809.cspec"),
    },
    #[cfg(feature = "mc6800")]
    EmbeddedFile {
        processor: "MC6800",
        path: "6809.pspec",
        data: include_bytes!("../languages/MC6800/6809.pspec"),
    },
    #[cfg(feature = "mc6800")]
    EmbeddedFile {
        processor: "MC6800",
        path: "6809.sla",
        data: include_bytes!("../languages/MC6800/6809.sla"),
    },
    #[cfg(feature = "mc6800")]
    EmbeddedFile {
        processor: "MC6800",
        path: "H6309.sla",
        data: include_bytes!("../languages/MC6800/H6309.sla"),
    },
    #[cfg(feature = "mcs96")]
    EmbeddedFile {
        processor: "MCS96",
        path: "MCS96.cspec",
        data: include_bytes!("../languages/MCS96/MCS96.cspec"),
    },
    #[cfg(feature = "mcs96")]
    EmbeddedFile {
        processor: "MCS96",
        path: "MCS96.ldefs",
        data: include_bytes!("../languages/MCS96/MCS96.ldefs"),
    },
    #[cfg(feature = "mcs96")]
    EmbeddedFile {
        processor: "MCS96",
        path: "MCS96.pspec",
        data: include_bytes!("../languages/MCS96/MCS96.pspec"),
    },
    #[cfg(feature = "mcs96")]
    EmbeddedFile {
        processor: "MCS96",
        path: "MCS96.sla",
        data: include_bytes!("../languages/MCS96/MCS96.sla"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips.ldefs",
        data: include_bytes!("../languages/MIPS/mips.ldefs"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32.pspec",
        data: include_bytes!("../languages/MIPS/mips32.pspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32R6.pspec",
        data: include_bytes!("../languages/MIPS/mips32R6.pspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32R6be.sla",
        data: include_bytes!("../languages/MIPS/mips32R6be.sla"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32R6le.sla",
        data: include_bytes!("../languages/MIPS/mips32R6le.sla"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32_16e.pspec",
        data: include_bytes!("../languages/MIPS/mips32_16e.pspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32_eabi.cspec",
        data: include_bytes!("../languages/MIPS/mips32_eabi.cspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32_fp64.cspec",
        data: include_bytes!("../languages/MIPS/mips32_fp64.cspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32be.cspec",
        data: include_bytes!("../languages/MIPS/mips32be.cspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32be.sla",
        data: include_bytes!("../languages/MIPS/mips32be.sla"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32le.cspec",
        data: include_bytes!("../languages/MIPS/mips32le.cspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32le.sla",
        data: include_bytes!("../languages/MIPS/mips32le.sla"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips32micro.pspec",
        data: include_bytes!("../languages/MIPS/mips32micro.pspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips64.pspec",
        data: include_bytes!("../languages/MIPS/mips64.pspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips64R6.pspec",
        data: include_bytes!("../languages/MIPS/mips64R6.pspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips64_16e.pspec",
        data: include_bytes!("../languages/MIPS/mips64_16e.pspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips64_32_n32.cspec",
        data: include_bytes!("../languages/MIPS/mips64_32_n32.cspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips64_32_o32.cspec",
        data: include_bytes!("../languages/MIPS/mips64_32_o32.cspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips64_32_o64.cspec",
        data: include_bytes!("../languages/MIPS/mips64_32_o64.cspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips64be.cspec",
        data: include_bytes!("../languages/MIPS/mips64be.cspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips64be.sla",
        data: include_bytes!("../languages/MIPS/mips64be.sla"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips64le.cspec",
        data: include_bytes!("../languages/MIPS/mips64le.cspec"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips64le.sla",
        data: include_bytes!("../languages/MIPS/mips64le.sla"),
    },
    #[cfg(feature = "mips")]
    EmbeddedFile {
        processor: "MIPS",
        path: "mips64micro.pspec",
        data: include_bytes!("../languages/MIPS/mips64micro.pspec"),
    },
    #[cfg(feature = "nds32")]
    EmbeddedFile {
        processor: "NDS32",
        path: "nds32.cspec",
        data: include_bytes!("../languages/NDS32/nds32.cspec"),
    },
    #[cfg(feature = "nds32")]
    EmbeddedFile {
        processor: "NDS32",
        path: "nds32.ldefs",
        data: include_bytes!("../languages/NDS32/nds32.ldefs"),
    },
    #[cfg(feature = "nds32")]
    EmbeddedFile {
        processor: "NDS32",
        path: "nds32.pspec",
        data: include_bytes!("../languages/NDS32/nds32.pspec"),
    },
    #[cfg(feature = "nds32")]
    EmbeddedFile {
        processor: "NDS32",
        path: "nds32be.sla",
        data: include_bytes!("../languages/NDS32/nds32be.sla"),
    },
    #[cfg(feature = "nds32")]
    EmbeddedFile {
        processor: "NDS32",
        path: "nds32le.sla",
        data: include_bytes!("../languages/NDS32/nds32le.sla"),
    },
    #[cfg(feature = "pa-risc")]
    EmbeddedFile {
        processor: "PA-RISC",
        path: "pa-risc.ldefs",
        data: include_bytes!("../languages/PA-RISC/pa-risc.ldefs"),
    },
    #[cfg(feature = "pa-risc")]
    EmbeddedFile {
        processor: "PA-RISC",
        path: "pa-risc32.cspec",
        data: include_bytes!("../languages/PA-RISC/pa-risc32.cspec"),
    },
    #[cfg(feature = "pa-risc")]
    EmbeddedFile {
        processor: "PA-RISC",
        path: "pa-risc32.pspec",
        data: include_bytes!("../languages/PA-RISC/pa-risc32.pspec"),
    },
    #[cfg(feature = "pa-risc")]
    EmbeddedFile {
        processor: "PA-RISC",
        path: "pa-risc32be.sla",
        data: include_bytes!("../languages/PA-RISC/pa-risc32be.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "PIC24.cspec",
        data: include_bytes!("../languages/PIC/PIC24.cspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "PIC24.ldefs",
        data: include_bytes!("../languages/PIC/PIC24.ldefs"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "PIC24.pspec",
        data: include_bytes!("../languages/PIC/PIC24.pspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "PIC24E.sla",
        data: include_bytes!("../languages/PIC/PIC24E.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "PIC24F.sla",
        data: include_bytes!("../languages/PIC/PIC24F.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "PIC24H.sla",
        data: include_bytes!("../languages/PIC/PIC24H.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "dsPIC30F.sla",
        data: include_bytes!("../languages/PIC/dsPIC30F.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "dsPIC33C.sla",
        data: include_bytes!("../languages/PIC/dsPIC33C.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "dsPIC33E.sla",
        data: include_bytes!("../languages/PIC/dsPIC33E.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "dsPIC33F.sla",
        data: include_bytes!("../languages/PIC/dsPIC33F.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic12c5xx.cspec",
        data: include_bytes!("../languages/PIC/pic12c5xx.cspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic12c5xx.ldefs",
        data: include_bytes!("../languages/PIC/pic12c5xx.ldefs"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic12c5xx.pspec",
        data: include_bytes!("../languages/PIC/pic12c5xx.pspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic12c5xx.sla",
        data: include_bytes!("../languages/PIC/pic12c5xx.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic16.cspec",
        data: include_bytes!("../languages/PIC/pic16.cspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic16.ldefs",
        data: include_bytes!("../languages/PIC/pic16.ldefs"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic16.pspec",
        data: include_bytes!("../languages/PIC/pic16.pspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic16.sla",
        data: include_bytes!("../languages/PIC/pic16.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic16c5x.cspec",
        data: include_bytes!("../languages/PIC/pic16c5x.cspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic16c5x.ldefs",
        data: include_bytes!("../languages/PIC/pic16c5x.ldefs"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic16c5x.pspec",
        data: include_bytes!("../languages/PIC/pic16c5x.pspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic16c5x.sla",
        data: include_bytes!("../languages/PIC/pic16c5x.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic16f.cspec",
        data: include_bytes!("../languages/PIC/pic16f.cspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic16f.pspec",
        data: include_bytes!("../languages/PIC/pic16f.pspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic16f.sla",
        data: include_bytes!("../languages/PIC/pic16f.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic17c7xx.cspec",
        data: include_bytes!("../languages/PIC/pic17c7xx.cspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic17c7xx.ldefs",
        data: include_bytes!("../languages/PIC/pic17c7xx.ldefs"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic17c7xx.pspec",
        data: include_bytes!("../languages/PIC/pic17c7xx.pspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic17c7xx.sla",
        data: include_bytes!("../languages/PIC/pic17c7xx.sla"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic18.cspec",
        data: include_bytes!("../languages/PIC/pic18.cspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic18.ldefs",
        data: include_bytes!("../languages/PIC/pic18.ldefs"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic18.pspec",
        data: include_bytes!("../languages/PIC/pic18.pspec"),
    },
    #[cfg(feature = "pic")]
    EmbeddedFile {
        processor: "PIC",
        path: "pic18.sla",
        data: include_bytes!("../languages/PIC/pic18.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc.ldefs",
        data: include_bytes!("../languages/PowerPC/ppc.ldefs"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32.cspec",
        data: include_bytes!("../languages/PowerPC/ppc_32.cspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32.pspec",
        data: include_bytes!("../languages/PowerPC/ppc_32.pspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_4xx_be.sla",
        data: include_bytes!("../languages/PowerPC/ppc_32_4xx_be.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_4xx_le.sla",
        data: include_bytes!("../languages/PowerPC/ppc_32_4xx_le.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_be.sla",
        data: include_bytes!("../languages/PowerPC/ppc_32_be.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_be_Mac.cspec",
        data: include_bytes!("../languages/PowerPC/ppc_32_be_Mac.cspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_e500_be.cspec",
        data: include_bytes!("../languages/PowerPC/ppc_32_e500_be.cspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_e500_be.sla",
        data: include_bytes!("../languages/PowerPC/ppc_32_e500_be.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_e500_le.cspec",
        data: include_bytes!("../languages/PowerPC/ppc_32_e500_le.cspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_e500_le.sla",
        data: include_bytes!("../languages/PowerPC/ppc_32_e500_le.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_e500mc_be.cspec",
        data: include_bytes!("../languages/PowerPC/ppc_32_e500mc_be.cspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_e500mc_be.sla",
        data: include_bytes!("../languages/PowerPC/ppc_32_e500mc_be.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_e500mc_le.cspec",
        data: include_bytes!("../languages/PowerPC/ppc_32_e500mc_le.cspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_e500mc_le.sla",
        data: include_bytes!("../languages/PowerPC/ppc_32_e500mc_le.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_le.sla",
        data: include_bytes!("../languages/PowerPC/ppc_32_le.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_mpc8270.pspec",
        data: include_bytes!("../languages/PowerPC/ppc_32_mpc8270.pspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_quicciii_be.sla",
        data: include_bytes!("../languages/PowerPC/ppc_32_quicciii_be.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_32_quicciii_le.sla",
        data: include_bytes!("../languages/PowerPC/ppc_32_quicciii_le.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64.pspec",
        data: include_bytes!("../languages/PowerPC/ppc_64.pspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_32.cspec",
        data: include_bytes!("../languages/PowerPC/ppc_64_32.cspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_be.cspec",
        data: include_bytes!("../languages/PowerPC/ppc_64_be.cspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_be.sla",
        data: include_bytes!("../languages/PowerPC/ppc_64_be.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_be_Mac.cspec",
        data: include_bytes!("../languages/PowerPC/ppc_64_be_Mac.cspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_isa_altivec_be.sla",
        data: include_bytes!("../languages/PowerPC/ppc_64_isa_altivec_be.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_isa_altivec_le.sla",
        data: include_bytes!("../languages/PowerPC/ppc_64_isa_altivec_le.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_isa_altivec_vle_be.sla",
        data: include_bytes!("../languages/PowerPC/ppc_64_isa_altivec_vle_be.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_isa_be.sla",
        data: include_bytes!("../languages/PowerPC/ppc_64_isa_be.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_isa_le.sla",
        data: include_bytes!("../languages/PowerPC/ppc_64_isa_le.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_isa_vle_be.sla",
        data: include_bytes!("../languages/PowerPC/ppc_64_isa_vle_be.sla"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_le.cspec",
        data: include_bytes!("../languages/PowerPC/ppc_64_le.cspec"),
    },
    #[cfg(feature = "powerpc")]
    EmbeddedFile {
        processor: "PowerPC",
        path: "ppc_64_le.sla",
        data: include_bytes!("../languages/PowerPC/ppc_64_le.sla"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "RV32.pspec",
        data: include_bytes!("../languages/RISCV/RV32.pspec"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "RV64.pspec",
        data: include_bytes!("../languages/RISCV/RV64.pspec"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "andestar_v5.ldefs",
        data: include_bytes!("../languages/RISCV/andestar_v5.ldefs"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "andestar_v5.sla",
        data: include_bytes!("../languages/RISCV/andestar_v5.sla"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "riscv.ilp32d.sla",
        data: include_bytes!("../languages/RISCV/riscv.ilp32d.sla"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "riscv.ldefs",
        data: include_bytes!("../languages/RISCV/riscv.ldefs"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "riscv.lp64d.sla",
        data: include_bytes!("../languages/RISCV/riscv.lp64d.sla"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "riscv32-fp.cspec",
        data: include_bytes!("../languages/RISCV/riscv32-fp.cspec"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "riscv32.cspec",
        data: include_bytes!("../languages/RISCV/riscv32.cspec"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "riscv64-fp.cspec",
        data: include_bytes!("../languages/RISCV/riscv64-fp.cspec"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "riscv64.cspec",
        data: include_bytes!("../languages/RISCV/riscv64.cspec"),
    },
    #[cfg(feature = "riscv")]
    EmbeddedFile {
        processor: "RISCV",
        path: "old/riscv_deprecated.ldefs",
        data: include_bytes!("../languages/RISCV/old/riscv_deprecated.ldefs"),
    },
    #[cfg(feature = "sparc")]
    EmbeddedFile {
        processor: "Sparc",
        path: "SparcV9.ldefs",
        data: include_bytes!("../languages/Sparc/SparcV9.ldefs"),
    },
    #[cfg(feature = "sparc")]
    EmbeddedFile {
        processor: "Sparc",
        path: "SparcV9.pspec",
        data: include_bytes!("../languages/Sparc/SparcV9.pspec"),
    },
    #[cfg(feature = "sparc")]
    EmbeddedFile {
        processor: "Sparc",
        path: "SparcV9_32.cspec",
        data: include_bytes!("../languages/Sparc/SparcV9_32.cspec"),
    },
    #[cfg(feature = "sparc")]
    EmbeddedFile {
        processor: "Sparc",
        path: "SparcV9_32.sla",
        data: include_bytes!("../languages/Sparc/SparcV9_32.sla"),
    },
    #[cfg(feature = "sparc")]
    EmbeddedFile {
        processor: "Sparc",
        path: "SparcV9_64.cspec",
        data: include_bytes!("../languages/Sparc/SparcV9_64.cspec"),
    },
    #[cfg(feature = "sparc")]
    EmbeddedFile {
        processor: "Sparc",
        path: "SparcV9_64.sla",
        data: include_bytes!("../languages/Sparc/SparcV9_64.sla"),
    },
    #[cfg(feature = "superh")]
    EmbeddedFile {
        processor: "SuperH",
        path: "sh-1.sla",
        data: include_bytes!("../languages/SuperH/sh-1.sla"),
    },
    #[cfg(feature = "superh")]
    EmbeddedFile {
        processor: "SuperH",
        path: "sh-2.sla",
        data: include_bytes!("../languages/SuperH/sh-2.sla"),
    },
    #[cfg(feature = "superh")]
    EmbeddedFile {
        processor: "SuperH",
        path: "sh-2a.sla",
        data: include_bytes!("../languages/SuperH/sh-2a.sla"),
    },
    #[cfg(feature = "superh")]
    EmbeddedFile {
        processor: "SuperH",
        path: "superh.cspec",
        data: include_bytes!("../languages/SuperH/superh.cspec"),
    },
    #[cfg(feature = "superh")]
    EmbeddedFile {
        processor: "SuperH",
        path: "superh.ldefs",
        data: include_bytes!("../languages/SuperH/superh.ldefs"),
    },
    #[cfg(feature = "superh")]
    EmbeddedFile {
        processor: "SuperH",
        path: "superh.pspec",
        data: include_bytes!("../languages/SuperH/superh.pspec"),
    },
    #[cfg(feature = "superh")]
    EmbeddedFile {
        processor: "SuperH",
        path: "superh2a.cspec",
        data: include_bytes!("../languages/SuperH/superh2a.cspec"),
    },
    #[cfg(feature = "superh4")]
    EmbeddedFile {
        processor: "SuperH4",
        path: "SuperH4.ldefs",
        data: include_bytes!("../languages/SuperH4/SuperH4.ldefs"),
    },
    #[cfg(feature = "superh4")]
    EmbeddedFile {
        processor: "SuperH4",
        path: "SuperH4.pspec",
        data: include_bytes!("../languages/SuperH4/SuperH4.pspec"),
    },
    #[cfg(feature = "superh4")]
    EmbeddedFile {
        processor: "SuperH4",
        path: "SuperH4_be.cspec",
        data: include_bytes!("../languages/SuperH4/SuperH4_be.cspec"),
    },
    #[cfg(feature = "superh4")]
    EmbeddedFile {
        processor: "SuperH4",
        path: "SuperH4_be.sla",
        data: include_bytes!("../languages/SuperH4/SuperH4_be.sla"),
    },
    #[cfg(feature = "superh4")]
    EmbeddedFile {
        processor: "SuperH4",
        path: "SuperH4_le.cspec",
        data: include_bytes!("../languages/SuperH4/SuperH4_le.cspec"),
    },
    #[cfg(feature = "superh4")]
    EmbeddedFile {
        processor: "SuperH4",
        path: "SuperH4_le.sla",
        data: include_bytes!("../languages/SuperH4/SuperH4_le.sla"),
    },
    #[cfg(feature = "ti_msp430")]
    EmbeddedFile {
        processor: "TI_MSP430",
        path: "TI_MSP430.cspec",
        data: include_bytes!("../languages/TI_MSP430/TI_MSP430.cspec"),
    },
    #[cfg(feature = "ti_msp430")]
    EmbeddedFile {
        processor: "TI_MSP430",
        path: "TI_MSP430.ldefs",
        data: include_bytes!("../languages/TI_MSP430/TI_MSP430.ldefs"),
    },
    #[cfg(feature = "ti_msp430")]
    EmbeddedFile {
        processor: "TI_MSP430",
        path: "TI_MSP430.pspec",
        data: include_bytes!("../languages/TI_MSP430/TI_MSP430.pspec"),
    },
    #[cfg(feature = "ti_msp430")]
    EmbeddedFile {
        processor: "TI_MSP430",
        path: "TI_MSP430.sla",
        data: include_bytes!("../languages/TI_MSP430/TI_MSP430.sla"),
    },
    #[cfg(feature = "ti_msp430")]
    EmbeddedFile {
        processor: "TI_MSP430",
        path: "TI_MSP430X.cspec",
        data: include_bytes!("../languages/TI_MSP430/TI_MSP430X.cspec"),
    },
    #[cfg(feature = "ti_msp430")]
    EmbeddedFile {
        processor: "TI_MSP430",
        path: "TI_MSP430X.sla",
        data: include_bytes!("../languages/TI_MSP430/TI_MSP430X.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy.cspec",
        data: include_bytes!("../languages/Toy/toy.cspec"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy.ldefs",
        data: include_bytes!("../languages/Toy/toy.ldefs"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy.pspec",
        data: include_bytes!("../languages/Toy/toy.pspec"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy64-long8.cspec",
        data: include_bytes!("../languages/Toy/toy64-long8.cspec"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy64.cspec",
        data: include_bytes!("../languages/Toy/toy64.cspec"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy64_be.sla",
        data: include_bytes!("../languages/Toy/toy64_be.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy64_be_harvard.sla",
        data: include_bytes!("../languages/Toy/toy64_be_harvard.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy64_be_harvard_rev.sla",
        data: include_bytes!("../languages/Toy/toy64_be_harvard_rev.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy64_le.sla",
        data: include_bytes!("../languages/Toy/toy64_le.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toyPosStack.cspec",
        data: include_bytes!("../languages/Toy/toyPosStack.cspec"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy_be.sla",
        data: include_bytes!("../languages/Toy/toy_be.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy_be_posStack.sla",
        data: include_bytes!("../languages/Toy/toy_be_posStack.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy_builder_be.sla",
        data: include_bytes!("../languages/Toy/toy_builder_be.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy_builder_be_align2.sla",
        data: include_bytes!("../languages/Toy/toy_builder_be_align2.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy_builder_le.sla",
        data: include_bytes!("../languages/Toy/toy_builder_le.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy_builder_le_align2.sla",
        data: include_bytes!("../languages/Toy/toy_builder_le_align2.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy_harvard.pspec",
        data: include_bytes!("../languages/Toy/toy_harvard.pspec"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy_le.sla",
        data: include_bytes!("../languages/Toy/toy_le.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy_wsz_be.sla",
        data: include_bytes!("../languages/Toy/toy_wsz_be.sla"),
    },
    #[cfg(feature = "toy")]
    EmbeddedFile {
        processor: "Toy",
        path: "toy_wsz_le.sla",
        data: include_bytes!("../languages/Toy/toy_wsz_le.sla"),
    },
    #[cfg(feature = "tricore")]
    EmbeddedFile {
        processor: "tricore",
        path: "tc172x.pspec",
        data: include_bytes!("../languages/tricore/tc172x.pspec"),
    },
    #[cfg(feature = "tricore")]
    EmbeddedFile {
        processor: "tricore",
        path: "tc176x.pspec",
        data: include_bytes!("../languages/tricore/tc176x.pspec"),
    },
    #[cfg(feature = "tricore")]
    EmbeddedFile {
        processor: "tricore",
        path: "tc29x.pspec",
        data: include_bytes!("../languages/tricore/tc29x.pspec"),
    },
    #[cfg(feature = "tricore")]
    EmbeddedFile {
        processor: "tricore",
        path: "tricore.cspec",
        data: include_bytes!("../languages/tricore/tricore.cspec"),
    },
    #[cfg(feature = "tricore")]
    EmbeddedFile {
        processor: "tricore",
        path: "tricore.ldefs",
        data: include_bytes!("../languages/tricore/tricore.ldefs"),
    },
    #[cfg(feature = "tricore")]
    EmbeddedFile {
        processor: "tricore",
        path: "tricore.pspec",
        data: include_bytes!("../languages/tricore/tricore.pspec"),
    },
    #[cfg(feature = "tricore")]
    EmbeddedFile {
        processor: "tricore",
        path: "tricore.sla",
        data: include_bytes!("../languages/tricore/tricore.sla"),
    },
    #[cfg(feature = "v850")]
    EmbeddedFile {
        processor: "V850",
        path: "V850.cspec",
        data: include_bytes!("../languages/V850/V850.cspec"),
    },
    #[cfg(feature = "v850")]
    EmbeddedFile {
        processor: "V850",
        path: "V850.ldefs",
        data: include_bytes!("../languages/V850/V850.ldefs"),
    },
    #[cfg(feature = "v850")]
    EmbeddedFile {
        processor: "V850",
        path: "V850.pspec",
        data: include_bytes!("../languages/V850/V850.pspec"),
    },
    #[cfg(feature = "v850")]
    EmbeddedFile {
        processor: "V850",
        path: "V850.sla",
        data: include_bytes!("../languages/V850/V850.sla"),
    },
    #[cfg(feature = "v850")]
    EmbeddedFile {
        processor: "V850",
        path: "V850e3.pspec",
        data: include_bytes!("../languages/V850/V850e3.pspec"),
    },
    #[cfg(feature = "v850")]
    EmbeddedFile {
        processor: "V850",
        path: "V850e3.sla",
        data: include_bytes!("../languages/V850/V850e3.sla"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86-16-real.pspec",
        data: include_bytes!("../languages/x86/x86-16-real.pspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86-16.cspec",
        data: include_bytes!("../languages/x86/x86-16.cspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86-16.pspec",
        data: include_bytes!("../languages/x86/x86-16.pspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86-32-golang.cspec",
        data: include_bytes!("../languages/x86/x86-32-golang.cspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86-64-compat32.pspec",
        data: include_bytes!("../languages/x86/x86-64-compat32.pspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86-64-gcc.cspec",
        data: include_bytes!("../languages/x86/x86-64-gcc.cspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86-64-golang.cspec",
        data: include_bytes!("../languages/x86/x86-64-golang.cspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86-64-win.cspec",
        data: include_bytes!("../languages/x86/x86-64-win.cspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86-64.pspec",
        data: include_bytes!("../languages/x86/x86-64.pspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86-64.sla",
        data: include_bytes!("../languages/x86/x86-64.sla"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86.ldefs",
        data: include_bytes!("../languages/x86/x86.ldefs"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86.pspec",
        data: include_bytes!("../languages/x86/x86.pspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86.sla",
        data: include_bytes!("../languages/x86/x86.sla"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86borland.cspec",
        data: include_bytes!("../languages/x86/x86borland.cspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86delphi.cspec",
        data: include_bytes!("../languages/x86/x86delphi.cspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86gcc.cspec",
        data: include_bytes!("../languages/x86/x86gcc.cspec"),
    },
    #[cfg(feature = "x86")]
    EmbeddedFile {
        processor: "x86",
        path: "x86win.cspec",
        data: include_bytes!("../languages/x86/x86win.cspec"),
    },
    #[cfg(feature = "xtensa")]
    EmbeddedFile {
        processor: "Xtensa",
        path: "xtensa.cspec",
        data: include_bytes!("../languages/Xtensa/xtensa.cspec"),
    },
    #[cfg(feature = "xtensa")]
    EmbeddedFile {
        processor: "Xtensa",
        path: "xtensa.ldefs",
        data: include_bytes!("../languages/Xtensa/xtensa.ldefs"),
    },
    #[cfg(feature = "xtensa")]
    EmbeddedFile {
        processor: "Xtensa",
        path: "xtensa.pspec",
        data: include_bytes!("../languages/Xtensa/xtensa.pspec"),
    },
    #[cfg(feature = "xtensa")]
    EmbeddedFile {
        processor: "Xtensa",
        path: "xtensa_be.sla",
        data: include_bytes!("../languages/Xtensa/xtensa_be.sla"),
    },
    #[cfg(feature = "xtensa")]
    EmbeddedFile {
        processor: "Xtensa",
        path: "xtensa_le.sla",
        data: include_bytes!("../languages/Xtensa/xtensa_le.sla"),
    },
    #[cfg(feature = "z80")]
    EmbeddedFile {
        processor: "Z80",
        path: "z180.pspec",
        data: include_bytes!("../languages/Z80/z180.pspec"),
    },
    #[cfg(feature = "z80")]
    EmbeddedFile {
        processor: "Z80",
        path: "z180.sla",
        data: include_bytes!("../languages/Z80/z180.sla"),
    },
    #[cfg(feature = "z80")]
    EmbeddedFile {
        processor: "Z80",
        path: "z182.pspec",
        data: include_bytes!("../languages/Z80/z182.pspec"),
    },
    #[cfg(feature = "z80")]
    EmbeddedFile {
        processor: "Z80",
        path: "z80.cspec",
        data: include_bytes!("../languages/Z80/z80.cspec"),
    },
    #[cfg(feature = "z80")]
    EmbeddedFile {
        processor: "Z80",
        path: "z80.ldefs",
        data: include_bytes!("../languages/Z80/z80.ldefs"),
    },
    #[cfg(feature = "z80")]
    EmbeddedFile {
        processor: "Z80",
        path: "z80.pspec",
        data: include_bytes!("../languages/Z80/z80.pspec"),
    },
    #[cfg(feature = "z80")]
    EmbeddedFile {
        processor: "Z80",
        path: "z80.sla",
        data: include_bytes!("../languages/Z80/z80.sla"),
    },
    #[cfg(feature = "z80")]
    EmbeddedFile {
        processor: "Z80",
        path: "z8401x.pspec",
        data: include_bytes!("../languages/Z80/z8401x.pspec"),
    },
];
