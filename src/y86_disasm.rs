use extprim::u128::u128;
use std::convert::Into;
use std::io::Write;
use std::io;

const Y86_REGISTERS: [&'static str; 16] = [
    "%rax", "%rcx", "%rdx", "%rbx",
    "%rsp", "%rbp", "%rsi", "%rdi",
    "%r8", "%r9", "%r10", "%r11",
    "%r12", "%r13", "%r14", "NONE"
];


pub fn name_register<T: Into<usize>>(i: T) -> &'static str {
    let i = i.into();
    if i < Y86_REGISTERS.len() {
        Y86_REGISTERS[i]
    } else {
        "unknown"
    }
}

const Y86_IFUNS: [&'static str; 7] = [
    "(always)", "le", "l", "e", "ne", "ge", "g"
];

fn name_cc(ifun: u8) -> &'static str {
    let ifun = ifun as usize;
    if ifun < Y86_IFUNS.len() {
        Y86_IFUNS[ifun]
    } else {
        "(unknown)"
    }
}

// returns number of bytes of instruction used
pub fn disassemble<W: Write>(w: &mut W, instruction: u128) -> Result<u8, io::Error> {
    let icode: u8 = (((instruction >> 4) & u128::new(0xF)) as u128).low64() as u8;
    let ifun: u8 = (instruction & u128::new(0xF)).low64() as u8;
    let ra: u8 = (((instruction >> 12) & u128::new(0xF)) as u128).low64() as u8;
    let rb: u8 = (((instruction >> 8) & u128::new(0xF)) as u128).low64() as u8;
    let disp: u64  = ((instruction >> 16) as u128).low64();
    let dest: u64 = ((instruction >> 8) as u128).low64();
    let used_bytes = match icode {
        0 => {
            write!(w, "halt")?;
            1
        },
        1 => {
            write!(w, "nop")?;
            1
        },
        2 => {
            match ifun {
                0 => write!(w, "rrmovq {}, {}", name_register(ra), name_register(rb))?,
                _ => write!(w, "cmov{} {}, {}", name_cc(ifun), name_register(ra), name_register(rb))?,
            };
            2
        },
        3 => {
            write!(w, "irmovq $0x{:x}, {}", disp, name_register(rb))?;
            10
        },
        4 => {
            write!(w, "rmmovq {}, 0x{:x}({})", name_register(ra), disp, name_register(rb))?;
            10
        },
        5 => {
            write!(w, "mrmovq 0x{:x}({}), {}", disp, name_register(rb), name_register(ra))?;
            10
        },
        6 => {
            let mnemonic = match ifun {
                0 => "addq",
                1 => "subq",
                2 => "andq",
                3 => "xorq",
                _ => "<unknown OPq>",
            };
            write!(w, "{} {}, {}", mnemonic, name_register(ra), name_register(rb))?;
            2
        },
        7 => {
            match ifun {
                0 => write!(w, "jmp 0x{:x}", dest)?,
                _ => write!(w, "j{} 0x{:x}", name_cc(ifun), dest)?,
            };
            9
        },
        8 => {
            write!(w, "call 0x{:x}", dest)?;
            9
        },
        9 => {
            write!(w, "ret")?;
            1
        },
        10 => {
            write!(w, "pushq {}", name_register(ra))?;
            2
        },
        11 => {
            write!(w, "popq {}", name_register(rb))?;
            2
        },
        _ => {
            write!(w, "<invalid>")?;
            0
        }
    };
    return Ok(used_bytes);
}

pub fn disassemble_to_string(instruction: u128) -> (u8, String) {
    let mut result = Vec::new();
    let bytes = disassemble(&mut result, instruction).unwrap();
    (bytes, String::from_utf8(result).unwrap())
}

#[cfg(tests)]
mod tests {
    #[test]
    fn simple() {
        assert_eq!(disassemble_to_string(u128::new(0x00)), (1, "halt"));
        assert_eq!(disassemble_to_string(u128::new(0x10)), (1, "nop"));
        assert_eq!(disassemble_to_string(u128::new(0x8920)), (2, "rrmovq %r8, %r9"));
        assert_eq!(disassemble_to_string(u128::new(0xDEADBEEF71)), (9, "jle 0xDEADBEEF"));
        assert_eq!(disassemble_to_string(u128::new(0x8961)), (2, "subq %r8, %r9"));
        assert_eq!(disassemble_to_string(u128::new(0xDEADBEEF8940)), (10, "rmmovq %r8, 0xDEADBEEF(%r9)"));
    }
}