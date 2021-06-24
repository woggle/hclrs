use ast::{Statement, SpannedExpr, Expr, ConstDecl, WireDecl, WireValue, WireValues, WireWidth, BinOpCode, UnOpCode, MuxOption};
use program::{Program, RunningProgram, Y86_PREAMBLE};
use parser::{ExprParser, WireDeclsParser, ConstDeclsParser, StatementsParser};
use lexer::{Lexer, Tok};
use errors::Error;
use super::*;

use lalrpop_util::{ErrorRecovery, ParseError};

use std::env;
use std::fs::{File, read_dir};
use std::io::{sink, Read, BufReader};
use std::path::Path;
use std::sync::Once;
extern crate env_logger;

static TEST_LOGGER_ONCE: Once = Once::new();

type ParseErrorType<'input> = ParseError<usize, Tok<'input>, Error>;
type ErrorRecoveryType<'input> = ErrorRecovery<usize, Tok<'input>, Error>;

pub fn init_logger() {
    TEST_LOGGER_ONCE.call_once(|| {
        env_logger::init()
    })
}

#[allow(non_snake_case)]
fn parse_Expr_str<'input>(errors: &mut Vec<ErrorRecoveryType<'input>>, s: &'input str) ->
        Result<SpannedExpr, ParseErrorType<'input>> {
    let lexer = Lexer::new(s);
    ExprParser::new().parse(errors, lexer)
}

#[allow(non_snake_case)]
fn parse_WireDecls_str<'input>(errors: &mut Vec<ErrorRecoveryType<'input>>, s: &'input str) ->
        Result<Vec<WireDecl>, ParseErrorType<'input>> {
    let lexer = Lexer::new(s);
    WireDeclsParser::new().parse(errors, lexer)
}


#[allow(non_snake_case)]
fn parse_ConstDecls_str<'input>(errors: &mut Vec<ErrorRecoveryType<'input>>, s: &'input str) ->
        Result<Vec<ConstDecl>, ParseErrorType<'input>> {
    let lexer = Lexer::new(s);
    ConstDeclsParser::new().parse(errors, lexer)
}

#[allow(non_snake_case)]
fn parse_Statements_str<'input>(
    errors: &mut Vec<ErrorRecoveryType<'input>>,
    s: &'input str) -> Result<Vec<Statement>, ParseErrorType<'input>> {
    let lexer = Lexer::new(s);
    StatementsParser::new().parse(errors, lexer)
}

fn strip_spans(mut expr: SpannedExpr) -> SpannedExpr {
    expr.apply_to_all_mut(&mut |item| {
        item.span = (0, 0);
        Ok(())
    }).unwrap();
    expr
}

#[test]
fn parse_binops() {
    let mut errors = Vec::new();
    assert_eq!(
        parse_Expr_str(&mut errors, "0b1000 * 15").unwrap(),
        SpannedExpr::new(
            (0, 11),
            Expr::BinOp(BinOpCode::Mul,
                SpannedExpr::new((0, 6), Expr::Constant(WireValue::from_binary("1000"))),
                SpannedExpr::new((9, 11), Expr::Constant(WireValue::from_decimal("15")))
            ),
        )
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "0b1000 * 15 + 1").unwrap(),
        SpannedExpr::new(
            (0, 15),
            Expr::BinOp(BinOpCode::Add,
                SpannedExpr::new(
                    (0, 11),
                    Expr::BinOp(BinOpCode::Mul,
                        SpannedExpr::new((0, 6), Expr::Constant(WireValue::from_binary("1000"))),
                        SpannedExpr::new((9, 11), Expr::Constant(WireValue::from_decimal("15")))
                    ),
                ),
                SpannedExpr::new((14, 15),
                    Expr::Constant(WireValue::from_decimal("1"))
                ),
            ),
        )
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "0b1000 + 15 * 1").unwrap(),
        SpannedExpr::new(
            (0, 15),
            Expr::BinOp(BinOpCode::Add,
                SpannedExpr::new((0, 6), Expr::Constant(WireValue::from_binary("1000"))),
                SpannedExpr::new(
                    (9, 15),
                    Expr::BinOp(BinOpCode::Mul,
                        SpannedExpr::new((9, 11), Expr::Constant(WireValue::from_decimal("15"))),
                        SpannedExpr::new((14, 15), Expr::Constant(WireValue::from_decimal("1"))),
                    )
                ),
            ),
        )
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "0b1000 * 15 + 1 > 0").unwrap().to_expr(),
        &Expr::BinOp(BinOpCode::Greater,
            parse_Expr_str(&mut errors, "0b1000 * 15 + 1").unwrap(),
            SpannedExpr::new((18, 19), Expr::Constant(WireValue::from_decimal("0")))
        )
    );
    assert_eq!(
        strip_spans(
            parse_Expr_str(&mut errors, "  0b1000 & (15 + 1)  > 5  &&  0x1234 < 3  ||  4 >= 1  <<  1 / 5   ").unwrap()
        ),
        strip_spans(
            parse_Expr_str(&mut errors, "((0b1000 & (15 + 1)) > 5) && (0x1234 < 3) || (4 >= (1 << (1 / 5)))").unwrap()
        )
    );
}

#[test]
fn parse_unops() {
    let mut errors = Vec::new();
    assert_eq!(
        parse_Expr_str(&mut errors, "-0b1000").unwrap(),
        SpannedExpr::new((0, 7),
            Expr::UnOp(UnOpCode::Negate,
                SpannedExpr::new((1, 7), Expr::Constant(WireValue::from_binary("1000"))))
        )
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "1+-0b1000").unwrap(),
        SpannedExpr::new((0, 9), Expr::BinOp(BinOpCode::Add,
            SpannedExpr::new((0, 1), Expr::Constant(WireValue::from_decimal("1"))),
            SpannedExpr::new((2, 9), Expr::UnOp(UnOpCode::Negate,
                SpannedExpr::new((3, 9), Expr::Constant(WireValue::from_binary("1000")))))
        ))
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "~42").unwrap(),
        SpannedExpr::new((0, 3), Expr::UnOp(UnOpCode::Complement,
            SpannedExpr::new((1, 3), Expr::Constant(WireValue::from_decimal("42")))))
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "+42").unwrap(),
        SpannedExpr::new((0, 3), Expr::UnOp(UnOpCode::Plus,
            SpannedExpr::new((1, 3), Expr::Constant(WireValue::from_decimal("42")))))
    );
    assert_eq!(errors.len(), 0);
}

#[test]
fn parse_mux() {
    let mut errors = Vec::new();
    assert_eq!(
        parse_Expr_str(&mut errors, "[0:42;0x42:43;1:44;]").unwrap(),
        SpannedExpr::new((0, 20),
            Expr::Mux(vec!(
                MuxOption {
                    condition: SpannedExpr::new(
                        (1, 2),
                        Expr::Constant(WireValue::from_decimal("0"))
                    ),
                    value: SpannedExpr::new(
                        (3, 5),
                        Expr::Constant(WireValue::from_decimal("42"))
                    ),
                },
                MuxOption {
                    condition: SpannedExpr::new(
                        (6, 10),
                        Expr::Constant(WireValue::from_hexadecimal("42"))
                    ),
                    value: SpannedExpr::new(
                        (11, 13),
                        Expr::Constant(WireValue::from_decimal("43"))
                    ),
                },
                MuxOption {
                    condition: SpannedExpr::new(
                        (14, 15),
                        Expr::Constant(WireValue::from_decimal("1"))
                    ),
                    value: SpannedExpr::new(
                        (16, 18),
                        Expr::Constant(WireValue::from_decimal("44"))
                    ),
                }
            ))
        )
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "[0:42;0x42:43;1:44]").unwrap(),
        SpannedExpr::new((0, 19),
            Expr::Mux(vec!(
                MuxOption {
                    condition: SpannedExpr::new(
                        (1, 2),
                        Expr::Constant(WireValue::from_decimal("0"))
                    ),
                    value: SpannedExpr::new(
                        (3, 5),
                        Expr::Constant(WireValue::from_decimal("42"))
                    ),
                },
                MuxOption {
                    condition: SpannedExpr::new(
                        (6, 10),
                        Expr::Constant(WireValue::from_hexadecimal("42"))
                    ),
                    value: SpannedExpr::new(
                        (11, 13),
                        Expr::Constant(WireValue::from_decimal("43"))
                    ),
                },
                MuxOption {
                    condition: SpannedExpr::new(
                        (14, 15),
                        Expr::Constant(WireValue::from_decimal("1"))
                    ),
                    value: SpannedExpr::new(
                        (16, 18),
                        Expr::Constant(WireValue::from_decimal("44"))
                    ),
                }
            ))
        )
    );
    assert_eq!(errors.len(), 0);
}


#[test]
fn parse_wiredecls() {
    init_logger();
    let mut errors = Vec::new();
    assert_eq!(
        parse_WireDecls_str(&mut errors, "wire x : 32 , y : 2, z : 1").unwrap(),
        vec!(WireDecl { name: String::from("x"), width: WireWidth::Bits(32), span: (5, 11), },
             WireDecl { name: String::from("y"), width: WireWidth::Bits(2), span: (14, 19), },
             WireDecl { name: String::from("z"), width: WireWidth::Bits(1), span: (21, 26), })
    );
    assert_eq!(errors.len(), 0);
    errors.clear();
    assert_eq!(
        parse_WireDecls_str(&mut errors, "wire x : 64").unwrap(),
        vec!(WireDecl { name: String::from("x"), width: WireWidth::Bits(64), span: (5, 11), })
    );
    assert_eq!(errors.len(), 0);
}

#[test]
fn parse_constdecls() {
    init_logger();
    let mut errors = Vec::new();
    assert_eq!(
        parse_ConstDecls_str(&mut errors, "const x = 0x42, y=0").unwrap(),
        vec!(
            ConstDecl { name: String::from("x"), name_span: (6, 7), value: SpannedExpr::new( (10, 14),
                Expr::Constant(WireValue::from_hexadecimal("42"))
            ) },
            ConstDecl { name: String::from("y"), name_span: (16, 17), value: SpannedExpr::new( (18, 19),
                Expr::Constant(WireValue::from_decimal("0"))
            ) }
        )
    );
    assert_eq!(errors.len(), 0);
}

#[test]
fn eval_binaryops() {
    init_logger();
    let mut errors = Vec::new();
    assert_eq!(
        parse_Expr_str(&mut errors, "0b1000 & 15").unwrap().evaluate_constant().unwrap(),
        WireValue { bits: 8, width: WireWidth::Bits(4) }
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "0b1000 & 15 == 0x8").unwrap().evaluate_constant().unwrap(),
        WireValue { bits: 1, width: WireWidth::Bits(1) }
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "1 ^ 0xFFFF == 0xFFFE").unwrap().evaluate_constant().unwrap(),
        WireValue { bits: 1, width: WireWidth::Bits(1) }
    );
}

#[test]
fn eval_unops() {
    init_logger();
    let mut errors = Vec::new();
    assert_eq!(
        parse_Expr_str(&mut errors, "-0b1000").unwrap().evaluate_constant().unwrap(),
        WireValue::from_binary("1000")
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "-0b01000").unwrap().evaluate_constant().unwrap(),
        WireValue::from_binary("11000")
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "1+-0b01000").unwrap().evaluate_constant().unwrap(),
        WireValue::from_binary("11001")
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "~42").unwrap().evaluate_constant().unwrap(),
        WireValue { bits: !42, width: WireWidth::Unlimited }
    );
    assert_eq!(errors.len(), 0);
}

#[test]
fn eval_mux() {
    init_logger();
    let mut errors = Vec::new();
    assert_eq!(
        parse_Expr_str(&mut errors, "[ 0 : 42; 0x42 : 43 ; 1 : 44; ]").unwrap().evaluate_constant().unwrap(),
        WireValue { bits: 43, width: WireWidth::Unlimited }
    );
    // FIXME: more tests
}

#[test]
fn simple_program() {
    init_logger();
    let mut errors = Vec::new();
    let statements = parse_Statements_str(&mut errors,
        "const x = 42; wire y : 32; wire z : 32;
         z = y << 3; y = x * 2;").unwrap();
    debug!("statements are {:?}", statements);
    let program = Program::new(statements, vec!()).unwrap();
    let mut running_program = RunningProgram::new(program, 0, 0);
    let mut expect_values = WireValues::new();
    expect_values.insert(String::from("x"), WireValue::from_decimal("42"));
    assert_eq!(running_program.values(), &expect_values);
    running_program.step().unwrap();
    expect_values.insert(String::from("y"), WireValue::from_decimal("84").as_width(WireWidth::from(32)));
    expect_values.insert(String::from("z"), WireValue::from_decimal("672").as_width(WireWidth::from(32)));
    assert_eq!(running_program.values(), &expect_values);
}


#[test]
fn program_registers() {
    init_logger();
    let mut errors = Vec::new();
    let statements = parse_Statements_str(&mut errors,
        "register xY { a: 32 = 1; };
         x_a = Y_a + 1;").unwrap();
    let program = Program::new(statements, vec!()).unwrap();
    assert!(program.defaulted_wires().contains("stall_Y"));
    assert!(program.defaulted_wires().contains("bubble_Y"));
    let mut running_program = RunningProgram::new(program, 0, 0);
    assert_eq!(running_program.values().get("Y_a"), Some(&WireValue::from_decimal("1").as_width(WireWidth::from(32))));
    assert_eq!(running_program.values().get("x_a"), Some(&WireValue::from_decimal("1").as_width(WireWidth::from(32))));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("Y_a"), Some(&WireValue::from_decimal("2").as_width(WireWidth::from(32))));
    assert_eq!(running_program.values().get("x_a"), Some(&WireValue::from_decimal("2").as_width(WireWidth::from(32))));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("Y_a"), Some(&WireValue::from_decimal("3").as_width(WireWidth::from(32))));
    assert_eq!(running_program.values().get("x_a"), Some(&WireValue::from_decimal("3").as_width(WireWidth::from(32))));
}

#[test]
fn program_registers_stall() {
    init_logger();
    let mut errors = Vec::new();
    let statements = parse_Statements_str(&mut errors,
        "register xY { a: 32 = 1; };
         x_a = Y_a + 1;
         stall_Y = x_a > 2;").unwrap();
    let program = Program::new(statements, vec!()).unwrap();
    assert!(!program.defaulted_wires().contains("stall_Y"));
    assert!(program.defaulted_wires().contains("bubble_Y"));
    let mut running_program = RunningProgram::new(program, 0, 0);
    assert_eq!(running_program.values().get("Y_a"), Some(&WireValue::from_decimal("1").as_width(WireWidth::from(32))));
    assert_eq!(running_program.values().get("x_a"), Some(&WireValue::from_decimal("1").as_width(WireWidth::from(32))));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("Y_a"), Some(&WireValue::from_decimal("2").as_width(WireWidth::from(32))));
    assert_eq!(running_program.values().get("x_a"), Some(&WireValue::from_decimal("2").as_width(WireWidth::from(32))));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("Y_a"), Some(&WireValue::from_decimal("2").as_width(WireWidth::from(32))));
    assert_eq!(running_program.values().get("x_a"), Some(&WireValue::from_decimal("3").as_width(WireWidth::from(32))));
}

#[test]
fn program_registers_bubble() {
    init_logger();
    let mut errors = Vec::new();
    let statements = parse_Statements_str(&mut errors,
        "register xY { a: 32 = 1; };
         x_a = Y_a + 1;
         bubble_Y = x_a > 2;").unwrap();
    let program = Program::new(statements, vec!()).unwrap();
    assert!(program.defaulted_wires().contains("stall_Y"));
    assert!(!program.defaulted_wires().contains("bubble_Y"));
    let mut running_program = RunningProgram::new(program, 0, 0);
    assert_eq!(running_program.values().get("Y_a"), Some(&WireValue::from_decimal("1").as_width(WireWidth::from(32))));
    assert_eq!(running_program.values().get("x_a"), Some(&WireValue::from_decimal("1").as_width(WireWidth::from(32))));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("Y_a"), Some(&WireValue::from_decimal("2").as_width(WireWidth::from(32))));
    assert_eq!(running_program.values().get("x_a"), Some(&WireValue::from_decimal("2").as_width(WireWidth::from(32))));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("Y_a"), Some(&WireValue::from_decimal("1").as_width(WireWidth::from(32))));
    assert_eq!(running_program.values().get("x_a"), Some(&WireValue::from_decimal("3").as_width(WireWidth::from(32))));
}

#[test]
fn program_registers_and_mux() {
    init_logger();
    let mut errors = Vec::new();
    let statements = parse_Statements_str(&mut errors,
        "register xY { a: 32 = 42; };
         wire y : 32; wire z : 32;
         z = [Y_a > 43: 0; Y_a < 43: y << 3; Y_a == 43: 0; 1: 0];
         y = Y_a * 2;
         x_a = Y_a;").unwrap();
    let program = Program::new(statements, vec!()).unwrap();
    assert!(program.defaulted_wires().contains("stall_Y"));
    assert!(program.defaulted_wires().contains("bubble_Y"));
    let mut running_program = RunningProgram::new(program, 0, 0);
    let mut expect_values = WireValues::new();
    expect_values.insert(String::from("Y_a"), WireValue::from_decimal("42").as_width(WireWidth::from(32)));
    expect_values.insert(String::from("x_a"), WireValue::from_decimal("42").as_width(WireWidth::from(32)));
    expect_values.insert(String::from("y"), WireValue::from_decimal("84").as_width(WireWidth::from(32)));
    expect_values.insert(String::from("z"), WireValue::from_decimal("672").as_width(WireWidth::from(32)));
    expect_values.insert(String::from("stall_Y"), WireValue::from_decimal("0").as_width(WireWidth::from(1)));
    expect_values.insert(String::from("bubble_Y"), WireValue::from_decimal("0").as_width(WireWidth::from(1)));
    running_program.step().unwrap();
    assert_eq!(running_program.values(), &expect_values);
    running_program.step().unwrap();
    assert_eq!(running_program.values(), &expect_values);
}

#[test]
fn memory_program() {
    init_logger();
    let mut errors = Vec::new();
    let statements = parse_Statements_str(&mut errors,
        "register xX { count: 64 = 1; }
        mem_readbit = X_count & 1 == 1;
        mem_writebit = !mem_readbit;
        mem_addr = 0x8 + X_count;
        mem_input = 0x0123456789ABCDEF;
        x_count = X_count + 1;
        pc = 0; Stat = 1;
        ").unwrap();
    let program = Program::new_y86(statements).unwrap();
    let mut running_program = RunningProgram::new_y86(program);
    assert_eq!(running_program.values().get("X_count"), Some(&WireValue::from_decimal("1").as_width(WireWidth::from(64))));
    assert_eq!(running_program.values().get("x_count"), Some(&WireValue::from_decimal("1").as_width(WireWidth::from(64))));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("mem_output"), Some(&WireValue::from_decimal("0").as_width(WireWidth::from(64))));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("mem_output"), Some(&WireValue::from_decimal("0").as_width(WireWidth::from(64))));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("mem_output"), Some(&WireValue::from_hexadecimal("000123456789ABCD").as_width(WireWidth::from(64))));
}

#[test]
fn terminate_timeout() {
    init_logger();
    let mut errors = Vec::new();
    let statements = parse_Statements_str(&mut errors,
        "
        pc = 0; Stat = 1;
        ").unwrap();
    let program = Program::new_y86(statements).unwrap();
    let mut running_program = RunningProgram::new_y86(program);
    let mut options: RunOptions = Default::default();
    options.set_timeout(3);
    running_program.set_options(options);
    let mut result_vec = Vec::new();
    running_program.run(&mut result_vec).unwrap();
    let result_str = String::from_utf8(result_vec.clone()).unwrap();
    assert!(!result_str.contains("timed out"));
    running_program.dump_y86(&mut result_vec).unwrap();
    let result_str = String::from_utf8(result_vec).unwrap();
    assert_eq!(running_program.cycle(), 3);
    assert!(result_str.contains("timed out"));
}

#[test]
fn terminate_halt() {
    init_logger();
    let mut errors = Vec::new();
    let statements = parse_Statements_str(&mut errors,
        "
        register xX { count: 32 = 1; };
        x_count = X_count + 1;
        pc = 0; Stat = [
            X_count == 3 : 2;
            1: 1;
        ]
        ").unwrap();
    let program = Program::new_y86(statements).unwrap();
    let mut running_program = RunningProgram::new_y86(program);
    let mut options: RunOptions = Default::default();
    options.set_timeout(10);
    running_program.set_options(options);
    let mut result_vec = Vec::new();
    running_program.run(&mut result_vec).unwrap();
    let result_str = String::from_utf8(result_vec.clone()).unwrap();
    assert!(!result_str.contains("halted"));
    running_program.dump_y86(&mut result_vec).unwrap();
    let result_str = String::from_utf8(result_vec).unwrap();
    assert_eq!(running_program.cycle(), 3);
    assert!(result_str.contains("halted"));
}

#[test]
fn eval_bitselect() {
    init_logger();
    let mut errors = Vec::new();
    assert_eq!(
        parse_Expr_str(&mut errors, "0b1001011[1..4]").unwrap().evaluate_constant().unwrap(),
        WireValue::from_binary("101")
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "0b1001011[0..4]").unwrap().evaluate_constant().unwrap(),
        WireValue::from_binary("1011")
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "0b1001011[0..1]").unwrap().evaluate_constant().unwrap(),
        WireValue::from_binary("1")
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "0b10001011[7..8]").unwrap().evaluate_constant().unwrap(),
        WireValue::from_binary("1")
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "(0b1000 .. 0b1011)[7..8]").unwrap().evaluate_constant().unwrap(),
        WireValue::from_binary("1")
    );
    assert_eq!(errors.len(), 0);
}

#[test]
fn eval_bitconcat() {
    init_logger();
    let mut errors = Vec::new();
    assert_eq!(
        parse_Expr_str(&mut errors, "(0b100 .. 0b1011)").unwrap().evaluate_constant().unwrap(),
        WireValue::from_binary("1001011")
    );
    assert_eq!(
        parse_Expr_str(&mut errors, "(0b1 .. 0b0)").unwrap().evaluate_constant().unwrap(),
        WireValue::from_binary("10")
    );
    assert_eq!(errors.len(), 0);
}

#[test]
fn regfile_program() {
    init_logger();
    let mut errors = Vec::new();
    let statements = parse_Statements_str(&mut errors,
        "register xX { count: 64 = 0; }
        wire count: 64;
        count = X_count;
        reg_inputE = count + 24;
        reg_dstE = (count & 0xF)[0..4];
        reg_srcA = ((count - 1) & 0xF)[0..4];
        x_count = X_count + 1;
        pc = 0; Stat = 1;
        ").unwrap();
    let program = Program::new_y86(statements).unwrap();
    let mut running_program = RunningProgram::new_y86(program);
    running_program.step().unwrap();
    let width64 = WireWidth::from(64);
    assert_eq!(running_program.values().get("reg_outputA"), Some(&WireValue::from_decimal("0").as_width(width64)));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("reg_outputA"), Some(&WireValue::from_decimal("24").as_width(width64)));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("reg_outputA"), Some(&WireValue::from_decimal("25").as_width(width64)));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("reg_outputA"), Some(&WireValue::from_decimal("26").as_width(width64)));
    for _ in 3..16 {
        running_program.step().unwrap();
    }
    assert_eq!(running_program.values().get("reg_outputA"), Some(&WireValue::from_decimal("0").as_width(width64)));
    running_program.step().unwrap();
    assert_eq!(running_program.values().get("reg_outputA"), Some(&WireValue::from_decimal("40").as_width(width64)));
}

fn expect_execute(program: &Program, yo_path: &Path, expect_output_path: &Path) -> Result<(), Error> {
    debug!("expect_execute(..., {:?}, {:?})", yo_path, expect_output_path);
    let mut running_program = RunningProgram::new_y86((*program).clone());
    let mut yo_reader = BufReader::new(File::open(yo_path)?);
    running_program.load_memory_y86(&mut yo_reader)?;
    // FIXME: control with env var
    running_program.run(&mut sink())?;
    let result = running_program.dump_y86_str();
    let mut expect_output_reader = BufReader::new(File::open(expect_output_path)?);
    let mut expect_output = String::new();
    expect_output_reader.read_to_string(&mut expect_output)?;
    if !expect_output_path.to_str().unwrap().contains("poptest") {
        assert_eq!(expect_output, result,
            "reference:\n{}\nactual:\n{}\n", expect_output, result
        );
    } else {
        if expect_output != result {
            warn!("*** disagreement on poptest for {}", expect_output_path.to_str().unwrap());
        }
    }
    Ok(())
}

fn check_hcl_with_references(hcl_path: &Path, reference_dir: &Path, yo_dir: &Path) -> Result<(), Error> {
    let file_contents = read_y86_hcl(hcl_path)?;
    let program = parse_y86_hcl(&file_contents)?;
    for entry in read_dir(reference_dir).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name().to_str().unwrap().ends_with(".txt") {
            let ref_path = entry.path();
            let basename = ref_path.file_stem().unwrap();
            let mut yo_file = String::from(basename.to_str().unwrap());
            yo_file.push_str(".yo");
            let yo_file = yo_dir.join(yo_file);
            assert!(yo_file.is_file(), "{:?} is not file", yo_file);
            expect_execute(&program, yo_file.as_path(), ref_path.as_path())?;
        }
    }
    Ok(())
}

fn check_reference_dir(dir: &Path) {
    let mut errors = Vec::new();
    let mut entries = Vec::new();
    for entry in read_dir(dir).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name().to_str().unwrap().ends_with(".hcl") {
            entries.push(entry.path().to_owned());
        }
    }
    entries.sort();
    for entry in entries {
        let hcl_path = entry.as_path();
        debug!("found hcl {:?}", hcl_path);
        let basename = hcl_path.file_stem().unwrap();
        let mut reference_dir = String::from(basename.to_str().unwrap());
        reference_dir.push_str("-reference");
        let reference_dir = hcl_path.with_file_name(reference_dir);
        let yo_dir = hcl_path.with_file_name("y86");
        match check_hcl_with_references(hcl_path, reference_dir.as_path(),
                                  yo_dir.as_path()) {
            Err(e) => errors.push((hcl_path.to_owned(), e)),
            Ok(_) => {},
        }
    }
    if errors.len() > 0 {
        for (name, error) in errors {
            println!("{:?}: {:?}", name, error);
        }
        assert!(false);
    }
}

#[test] #[ignore]
fn external_reference() {
    init_logger();
    let mut dir = Path::new(&env::var("CARGO_MANIFEST_DIR").unwrap()).parent().unwrap().to_owned();
    dir.push("hclrs-testdata");
    assert!(dir.is_dir());
    check_reference_dir(&dir);
    let mut dir = Path::new(&env::var("CARGO_MANIFEST_DIR").unwrap()).parent().unwrap().to_owned();
    dir.push("hclrs-studentref");
    check_reference_dir(&dir);
}

fn get_errors_for(code: &str) -> String {
    let file_contents = FileContents::new_from_data(Y86_PREAMBLE, code, "test.hcl");
    match parse_y86_hcl(&file_contents) {
        Ok(_) => {
            panic!("expected compilation failure");
        },
        Err(e) => {
            let mut output: Vec<u8> = Vec::new();
            e.format_for_contents(&mut output, &file_contents).unwrap();
            return String::from_utf8(output).unwrap();
        }
    }
}

#[test]
fn error_mux_widths() {
    init_logger();
    let message = get_errors_for("
wire foo : 10, bar: 11, quux: 10;
foo = 0;
bar = 1;
quux = [
    foo > 42 : 1;
    foo > 3 : foo;
    foo < 3 : bar;
    1 : 0b0;
];
Stat = STAT_AOK;
pc = 0;
");
    debug!("error message is {}", message);
    assert!(message.contains("Mismatched wire widths for mux options"));
    assert!(message.contains("1 option is 10 bits wide"));
    assert!(message.contains("1 option is 11 bits wide"));
    assert!(message.contains("1 option is 1 bits wide"));
    assert!(message.contains("foo > 3 : foo;"));
    assert!(message.contains("foo < 3 : bar;"));
    assert!(message.contains("1 : 0b0;"));
}

#[test]
fn error_expr_widths() {
    init_logger();
    let message = get_errors_for("
wire foo : 10, bar: 11, quux: 10;
foo = 0;
bar = 1;
quux = foo
            &
       bar;
Stat = STAT_AOK;
pc = 0;
");
    debug!("error message is {}", message);
    assert!(message.contains("Mismatched wire widths."));
    assert!(message.contains("is 10 bits wide"));
    assert!(message.contains("is 11 bits wide"));
    assert!(message.contains("quux = foo"));
    assert!(message.contains("bar;"));
}

#[test]
fn error_wire_widths() {
    init_logger();
    let message = get_errors_for("
wire foo : 10, bar: 11;
foo = 0;
bar = foo;
Stat = STAT_AOK;
pc = 0;
");
    debug!("error message is {}", message);
    assert!(message.contains("Mismatched wire widths."));
    assert!(message.contains("The wire 'bar' is declared as 11 bits wide."));
    assert!(message.contains("a 10 bit wide value is assigned to it"));
    assert!(message.contains("foo;"));
}

#[test]
fn error_register_init_widths() {
    init_logger();
    let message = get_errors_for("
register xF {
    foo : 14 = 0b100;
};

x_foo = 1;

Stat = STAT_AOK;
pc = 0;
");
    debug!("error message is {}", message);
    assert!(message.contains("Register 'foo' in bank 'xF' is 14 bits wide, but "));
    assert!(message.contains("3 bits wide:"));
    assert!(message.contains("= 0b100"));
}

#[test]
fn error_duplicate_register() {
    init_logger();
    let message = get_errors_for("
register xF {
    foo : 14 = 0;
    foo : 14 = 0;
};

Stat = STAT_AOK;
pc = 0;
");
    debug!("error message is {}", message);
    assert!(message.contains("Register 'foo' in bank 'xF' defined twice."));
}

#[test]
fn error_undefined_wire_assign() {
    init_logger();
    let message = get_errors_for("
foo = 42;
Stat = STAT_AOK;
pc = 0;
");
    debug!("error message is {}", message);
    assert!(message.contains("Undeclared wire 'foo' assigned value:"));
    assert!(message.contains("foo = 42;"));
}

#[test]
fn error_undefined_wire_read() {
    init_logger();
    let message = get_errors_for("
wire foo : 16;
foo = bar + 42;
Stat = STAT_AOK;
pc = 0;
");
    debug!("error message is {}", message);
    assert!(message.contains("Usage of undeclared wire 'bar' in expression:"));
    assert!(message.contains("bar + 42"));
}

#[test]
fn error_nonconstant_wire_read_constant() {
    init_logger();
    let message = get_errors_for("
wire quux : 16;
const FOO = quux + 42;
quux = 42;
Stat = STAT_AOK;
pc = 0;
");
    debug!("error message is {}", message);
    assert!(message.contains("Usage of non-constant wire 'quux' in initial or constant value:"));
    assert!(message.contains("quux + 42"));
}

#[test]
fn error_unset_wire() {
    init_logger();
    let message = get_errors_for("
wire quux : 16;
Stat = STAT_AOK;
pc = 0;
");
    debug!("error message is {}", message);
    assert!(message.contains("Wire 'quux' never assigned but defined here:"));
    assert!(message.contains("quux : 16"));
}

#[test]
fn error_unset_builtin_wire_mandatory() {
    init_logger();
    let message = get_errors_for("
pc = 0;
");
    debug!("error message is {}", message);
    assert!(message.contains("Wire 'Stat' required by fixed functionality but never assigned."));
}

#[test]
fn error_unset_builtin_wire_inferred() {
    init_logger();
    let message = get_errors_for("
wire dummy : 64;
pc = 0;
Stat = STAT_AOK;
mem_readbit = 1;
dummy = mem_output;
");
    debug!("error message is {}", message);
    assert!(message.contains("Wire 'mem_addr' required by fixed functionality but never assigned."));
}

#[test]
fn error_redeclared_wire() {
    init_logger();
    let message = get_errors_for("
wire foo : 64;
wire foo : 32;
foo = 0;
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Wire 'foo' redeclared."));
    assert!(message.contains("foo : 64"));
    assert!(message.contains("foo : 32"));
}

#[test]
fn error_double_assigned_wire() {
    init_logger();
    let message = get_errors_for("
wire foo : 64;
foo = 0;
foo = 1;
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Wire 'foo' assigned twice. Assigned here:"));
    assert!(message.contains("foo = 0"));
    assert!(message.contains("foo = 1"));
}

#[test]
fn error_double_assigned_fixed_wire() {
    init_logger();
    let message = get_errors_for("
pc = 0;
i10bytes = 42;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Wire 'i10bytes' is output for fixed functionality but is assigned here:"));
    assert!(message.contains("i10bytes = 42"));
}

#[test]
fn error_redeclared_builtin_wire() {
    init_logger();
    let message = get_errors_for("
wire i10bytes : 64;
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Builtin wire 'i10bytes' redeclared here:"));
    assert!(message.contains("wire i10bytes : 64"));
}

#[test]
fn error_partial_fixed() {
    init_logger();
    let message = get_errors_for("
pc = 0;
Stat = STAT_AOK;
mem_addr = 0x42;
");
    debug!("error message is {}", message);
    assert!(message.contains("Wire 'mem_addr' set, but not the rest of this piece of fixed functionality."));
    assert!(message.contains("Did you mean to set mem_readbit?"));
    assert!(message.contains("Did you mean to set mem_input and mem_writebit?"));
}

#[test]
fn error_wire_loop() {
    init_logger();
    let message = get_errors_for("
wire quux : 64;
quux = i10bytes[0..64];
pc = quux + 42;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Circular dependency detected:"));
    assert!(message.contains("'i10bytes' depends on 'pc'"));
    assert!(message.contains("'pc' depends on 'quux'"));
    assert!(message.contains("'quux' depends on 'i10bytes'"));
}

#[test]
fn error_wire_loop_via_reg() {
    init_logger();
    let message = get_errors_for("
pc = 0;
Stat = STAT_AOK;
wire quux : 64;
reg_srcA = quux[0..4];
quux = reg_outputA;
");
    debug!("error message is {}", message);
    assert!(message.contains("Circular dependency detected:"));
    assert!(message.contains("'reg_srcA' depends on 'quux'"));
    assert!(message.contains("'quux' depends on 'reg_outputA'"));
    assert!(message.contains("'reg_outputA' depends on 'reg_srcA'"));
}

#[test]
fn error_wire_loop_via_memory() {
    init_logger();
    let message = get_errors_for("
pc = 0;
Stat = STAT_AOK;
wire quux : 64;
mem_addr = 0;
mem_readbit = quux[0..1];
quux = mem_output;
");
    debug!("error message is {}", message);
    assert!(message.contains("Circular dependency detected:"));
    assert!(message.contains("'mem_readbit' depends on 'quux'"));
    assert!(message.contains("'quux' depends on 'mem_output'"));
    assert!(message.contains("'mem_output' depends on 'mem_readbit'"));
}

#[test]
fn error_invalid_wire_width() {
    init_logger();
    let message = get_errors_for("
pc = 0;
Stat = STAT_AOK;
wire foo : 129;
");
    debug!("error message is {}", message);
    assert!(message.contains("Invalid wire width specified."));
}

#[test]
fn error_register_bank_name() {
    init_logger();
    let message = get_errors_for("
pc = 0;
Stat = STAT_AOK;
register badName {
    foo : 64 = 0;
}
");
    debug!("error message is {}", message);
    assert!(message.contains("Register bank name 'badName' invalid."));
}

#[test]
fn error_invalid_bit_index() {
    init_logger();
    let message = get_errors_for("
wire foo : 2;
foo = (i10bytes + 42)[79..81];
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Bit index '81' out of range for expression:"));
    assert!(message.contains("(i10bytes + 42)[79..81]"));
}

#[test]
#[cfg(feature="strict-boolean-ops")]
fn error_non_boolean_width() {
    init_logger();
    let message = get_errors_for("
wire foo : 1;
foo = (pc == 42) || (pc + 42);
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Non-boolean value used with boolean operator:"));
    assert!(message.contains("pc + 42"));
}

#[test]
fn error_non_bit_width() {
    init_logger();
    let message = get_errors_for("
wire foo : 88;
foo = (42 .. pc);
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Expression with unknown width used in bit concatenation:"));
    assert!(message.contains("42 .. pc"));
}

#[test]
fn error_misordered_indexes() {
    init_logger();
    let message = get_errors_for("
wire foo : 4;
foo = i10bytes[9..3];
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Bit selection expression selects less than 0 bits:"));
    assert!(message.contains("i10bytes[9..3]"));
}

#[test]
fn error_invalid_constant() {
    init_logger();
    let message = get_errors_for("
pc = 0x1234567890ABCDEF01234567890ABCDEFA;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Constant value is out of range:"));
    assert!(message.contains("0x123456789"));
}

#[test]
fn error_wire_too_wide() {
    init_logger();
    let message = get_errors_for("
wire foo : 64;
foo = (i10bytes .. i10bytes)[32..96];
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Expression would produce a value wider than supported (128 bits):"));
    assert!(message.contains("i10bytes .. i10bytes"));
}

#[test]
fn error_unterminated_comment() {
    init_logger();
    let message = get_errors_for("
wire foo : 64;
/* This is the start of the comment

which has more lines
");
    debug!("error message is {}", message);
    assert!(message.contains("Unterminated comment starting here:"));
    assert!(message.contains("This is the start of the comment"));
}

#[test]
fn error_missing_semicolon_statement() {
    init_logger();
    let message = get_errors_for("
pc = 0
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Unexpected token 'Stat', expected"));
    assert!(message.contains("Missing semicolon"));
}

#[test]
fn error_missing_semicolon_register() {
    init_logger();
    let message = get_errors_for("
register xF {
    foo : 10 = 0
    bar : 10 = 1
}
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Unexpected token 'bar', expected"));
    assert!(message.contains("Missing semicolon"));
}

#[test]
fn error_recovery_expr() {
    init_logger();
    let message = get_errors_for("
register xF {
    foo : 10 = 0
    bar : 10 = 1
}
register yZ {
    quux : 10 = 0
    baz : 10 = 1
}
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Unexpected token 'bar', expected"));
    assert!(message.contains("Unexpected token 'baz', expected"));
}

#[test]
fn error_recovery_register_decl() {
    init_logger();
    let message = get_errors_for("
register xF {
    foo : 10 = 0
    bar : 10 = 1
}
register yZ {
    >foo : 10 = 0;
    quux : 10 = 0
    baz : 10 = 1
}
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Unexpected token 'bar', expected"));
    assert!(message.contains("Unexpected token 'baz', expected"));
}

#[test]
fn error_recovery_statement() {
    init_logger();
    let message = get_errors_for("
wire foo : 32, bar : 32;
>foo = 0;
foo = 42
bar = foo;
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Unexpected token '>', expected"));
    assert!(message.contains("Unexpected token 'bar', expected"));
}

#[test]
fn error_summarize_binary_operators() {
    init_logger();
    let message = get_errors_for("
wire foo : 32, bar : 32;
foo = (bar bar);
bar = 42;
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Unexpected token 'bar', expected"));
    assert!(message.contains("a binary operator"));
    assert!(message.contains("a comparison operator"));
    assert!(message.contains("\'..\'"));
    assert!(message.contains("\'[\'"));
}

#[test]
fn error_double_equals() {
    init_logger();
    let message = get_errors_for("
wire foo : 32, bar : 32;
foo = (bar == bar == quux);
bar = 42;
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Unexpected token '==', expected"))
}


/* FIXME:
   This test is broken right now because the raw list of expected operators does
   not match what I expect. This may be an lalrpop issue.
*/
#[test]
#[ignore]
fn error_summarize_binary_operators_only() {
    init_logger();
    let message = get_errors_for("
wire foo : 32, bar : 32;
foo = (bar == bar quux);
bar = 42;
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Unexpected token 'quux', expected"));
    assert!(message.contains("a binary operator"));
    assert!(!message.contains("a comparison operator"));
    assert!(message.contains("\'..\'"));
    assert!(message.contains("\'[\'"));
}

#[test]
fn error_summarize_unary_operators() {
    init_logger();
    let message = get_errors_for("
wire foo : 32, bar : 32;
foo = (bar + );
bar = 42;
pc = 0;
Stat = STAT_AOK;
");
    debug!("error message is {}", message);
    assert!(message.contains("Unexpected token ')', expected"));
    assert!(message.contains("a unary operator"));
    assert!(message.contains("an identifier"));
    assert!(message.contains("an integer constant"));
    assert!(message.contains("\'[\'"));
}

#[test]
fn regression_symbol_type_mismatch() {
    init_logger();
    let mut errors = Vec::new();
    parse_Statements_str(&mut errors,
        "const CMOVXX = 0b0100;
         e_dstE = [ 1: 0; ]
         Stat = STAT_AOK;
         ").unwrap();
}

#[test]
fn regression_bogus_mux_width() {
    init_logger();
    let message = get_errors_for(
        "register eM { icode:4=0; dstE:4 = REG_NONE; }
         wire conditionsMet:1;
         conditionsMet = 0;
         e_icode  = CMOVXX;
         e_dstE = [ e_icode == CMOVXX &! conditionsMet:  REG_NONE; ];
         Stat = 0;
         pc = 0;
         ");
    assert!(message.contains("Mismatched wire widths"));
}

#[test]
fn error_recovery_midassignment() {
    init_logger();
    let message = get_errors_for(
        "foo := 1;
         Stat = STAT_AOK;
         pc = 0;
         ");
    debug!("error: {}", message);
    assert!(message.contains("Unexpected token ':', expected"));
    assert!(!message.contains("Found expression, expected"));
}

#[test]
fn error_recovery_missing_register_width1() {
    init_logger();
    // TODO: custom error for this case?
    let message = get_errors_for(
        "register xX {
            foo = 42;
            bar : 32 = * 42;
        }"
    );
    assert!(message.contains("Register declaration missing width"));
    assert!(message.contains("Unexpected token '*', expected"));
}

#[test]
fn error_recovery_missing_register_width2() {
    init_logger();
    let message = get_errors_for(
        "register xX {
            foo : = 42;
            bar : 32 = * 42;
        }"
    );
    assert!(message.contains("Unexpected token '=', expected"));
    assert!(message.contains("Unexpected token '*', expected"));
}

#[test]
fn error_recovery_register_early_semi() {
    init_logger();
    // TODO: custom error for this case?
    let message = get_errors_for(
        "register xX {
            foo;
            bar : 32 = * 42;
        }"
    );
    assert!(message.contains("Unexpected token ';', expected"));
    assert!(message.contains("Unexpected token '*', expected"));
}

#[test]
fn error_recovery_const_width() {
    init_logger();
    // TODO: custom error for this case?
    let message = get_errors_for(
        "const FOO : 42 = 0;
         const BAR * 42 = 0;"
    );
    assert!(message.contains("Constant declaration has unsupported"));
    assert!(message.contains("Unexpected token '*', expected"));
}

#[test]
fn error_recovery_wire_value_and_width() {
    init_logger();
    let message = get_errors_for(
        "wire foo : 42 = 0;
         wire foo : * 42;"
    );
    assert!(message.contains("declaration must be separate from assignment"));
    assert!(message.contains("Unexpected token '*', expected"));
}

#[test]
fn error_recovery_wire_value_no_width() {
    init_logger();
    let message = get_errors_for(
        "wire foo = 0;
         wire foo : * 42;"
    );
    debug!("message is {}", message);
    assert!(message.contains("declaration must be separate from assignment"));
    assert!(message.contains("missing width"));
    assert!(message.contains("Unexpected token '*', expected"));
}

#[test]
fn error_recovery_wire_no_value_no_width() {
    init_logger();
    let message = get_errors_for(
        "wire foo;
         wire foo : * 42;"
    );
    debug!("message is {}", message);
    assert!(message.contains("missing width"));
    assert!(message.contains("Unexpected token '*', expected"));
}

#[test]
fn error_recovery_assignment_width() {
    init_logger();
    // TODO: custom error for this case?
    let message = get_errors_for(
        "foo : 42 = 0;
         foo = * 42;"
    );
    assert!(message.contains("Unexpected token ':', expected"));
    assert!(message.contains("Unexpected token '*', expected"));
}

#[test]
fn error_recovery_bitslice_expr1() {
    init_logger();
    // TODO: custom error for this case?
    let message = get_errors_for(
        "foo = bar[quux + 1..3];
         foo = * bar;"
    );
    debug!("message is {}", message);
    assert!(message.contains("Unexpected token 'quux', expected"));
    assert!(message.contains("Unexpected token '*', expected"));
}

#[test]
fn error_recovery_bitslice_expr2() {
    init_logger();
    // TODO: custom error for this case?
    let message = get_errors_for(
        "foo = bar[1 + quux..3];
         foo = * bar;"
    );
    debug!("message is {}", message);
    assert!(message.contains("Unexpected token '+', expected"));
    assert!(message.contains("Unexpected token '*', expected"));
}

#[test]
fn error_recovery_bool_wire_and_colons() {
    init_logger();
    let message = get_errors_for(
        "bool mem_read = icode in { MRMOVQ };
         reg_srcA = [
                 icode in {RRMOVQ, CMOVXX, RMMOVQ, MRMOVQ, PUSHQ, OPQ} : opcode[8:12];
                 1 : REG_NONE;
         ];
         "
    );
    debug!("message is {}", message);
    assert!(message.contains("Unexpected token 'mem_read', expected"));
    assert!(message.contains("Unexpected token ':', expected"));
}

#[test]
fn error_colons_wire_index() {
    init_logger();
    let message = get_errors_for(
        "
         reg_srcA = [
                 icode in {RRMOVQ, CMOVXX, RMMOVQ, MRMOVQ, PUSHQ, OPQ} : opcode[8:12];
                 1 : REG_NONE;
         ];
         "
    );
    debug!("message is {}", message);
    assert!(message.contains("Unexpected token ':', expected"));
}

#[test]
fn error_colons_wire_concat() {
    init_logger();
    let message = get_errors_for(
        "
         reg_srcA = (opcode : opcode);
         "
    );
    debug!("message is {}", message);
    assert!(message.contains("Unexpected token ':', expected"));
}

#[test]
fn error_colons_wire_concat2() {
    init_logger();
    let message = get_errors_for(
        "
         reg_srcA = (opcode .. :);
         "
    );
    debug!("message is {}", message);
    assert!(message.contains("Unexpected token ':', expected"));
}

#[test]
fn error_colons_register_bank() {
    init_logger();
    let message = get_errors_for(
        "register :
         "
    );
    debug!("message is {}", message);
    // FIXME: this should output a better error than it currently does
    assert!(message.contains("Unexpected token "));
}

#[test]
fn error_colons_const_name() {
    init_logger();
    let message = get_errors_for(
        "const :
         "
    );
    debug!("message is {}", message);
    assert!(message.contains("Unexpected token ':', expected"));
}

#[test]
fn error_colons_after_register_bank() {
    init_logger();
    let message = get_errors_for(
        "register fD : 64
         "
    );
    debug!("message is {}", message);
    assert!(message.contains("Unexpected token ':', expected"));
}

#[test]
fn error_colons_after_register_bank2() {
    init_logger();
    let message = get_errors_for(
        "register fD {
            foo : 64 = 32;
        } : 64 = 42;
        "
    );
    debug!("message is {}", message);
    assert!(message.contains("Unexpected token ':', expected"));
}

#[test]
fn error_colons_register_name() {
    init_logger();
    let message = get_errors_for(
        "register fD { : 64
         "
    );
    debug!("message is {}", message);
    assert!(message.contains("Unexpected token ':', expected"));
}

#[test]
fn error_wire_decl_as_assign() {
    init_logger();
    let message = get_errors_for(
        "wire foo = 42;
         "
    );
    debug!("message is {}", message);
    assert!(message.contains("declaration must be separate from assignment"));
}

#[test]
fn error_colon_in_list1() {
    init_logger();
    let message = get_errors_for(
        "foo = bar in { FOO : QUUX }
         "
    );
    debug!("message is {}", message);
    assert!(message.contains("Unexpected token ':', expected"));
}

#[test]
fn error_colon_after_in1() {
    init_logger();
    let message = get_errors_for(
        "foo = bar in :
         "
    );
    debug!("message is {}", message);
    // FIXME: error could be better
    assert!(message.contains("Unexpected token "));
}

#[test]
fn error_pipeline_register_out_set() {
    init_logger();
    let message = get_errors_for(
        "register xY { foo : 1 = 0; }
        Y_foo = 1;
        x_foo = 0;
         "
    );
    debug!("message is {}", message);
    assert!(message.contains("assigned directly here"));
}

#[test]
fn error_register_in_not_set() {
    init_logger();
    let message = get_errors_for(
        "register xY { foo : 1 = 0; }
         "
    );
    debug!("message is {}", message);
    assert!(message.contains("input to the register defined here"));
    assert!(!message.contains("fixed functionality"));
}

#[test]
fn error_built_in_set_twice() {
    init_logger();
    let message = get_errors_for(
        "Stat = STAT_AOK; Stat = STAT_HLT; pc = 0;
         ");
    assert!(message.contains("Wire 'Stat' assigned"));
}

#[test]
fn error_register_in_set_twice() {
    init_logger();
    let message = get_errors_for(
        "register xY { foo : 1 = 0; } x_foo = 1; x_foo = 2;
         ");
    assert!(message.contains("Wire 'x_foo' assigned"));
}

#[test]
fn error_duplicate_register_out() {
    init_logger();
    let message = get_errors_for(
        "register xY { foo : 1 = 0; }
         register zY { foo : 1 = 0; }
         x_foo = 1; z_foo = 2;
         Stat = STAT_AOK;
         pc = 0;
         ");
    debug!("message is {}", message);
    assert!(message.contains("'Y_foo'"));
}

#[test]
fn error_missing_equals_on_mux() {
    init_logger();
    let message = get_errors_for(
        "wire foo: 32;
         foo [
            pc == 0: 1;
            1: 42;
         ];
         Stat = STAT_AOK;
         pc = 0;
         ");
    debug!("message is {}", message);
    assert!(message.contains("missing '='"));
}

#[test]
fn error_wire_declared_in_register_bank() {
    init_logger();
    let message = get_errors_for(
        "register xY {
            wire foo: 32 = 0;
         }
         Stat = STAT_AOK;
         pc = 0;
         ");
    debug!("message is {}", message);
    assert!(message.contains("'wire' to declare"));
}

#[test]
fn debug_output() {
    init_logger();
    let mut errors = Vec::new();
    let statements = parse_Statements_str(&mut errors,
        "wire foo_bar_baz_quux : 32;
        foo_bar_baz_quux = 0x42;
        Stat = 0;
        pc = 0;
        ").unwrap();
    let program = Program::new_y86(statements).unwrap();
    let mut running_program = RunningProgram::new_y86(program);
    let mut options = RunOptions::default();
    options.set_debug();
    running_program.set_options(options);
    let mut result: Vec<u8> = Vec::new();
    running_program.step_with_output(&mut result).unwrap();
    let result_as_string = String::from_utf8_lossy(result.as_slice()).into_owned();
    debug!("result is {:?}", result_as_string);
    assert!(result_as_string.contains("foo_bar_baz_quux              0x00000042"));
    assert!(result_as_string.contains("i10bytes          0x00000000000000000000"));
}


#[test]
fn debug_output_register() {
    init_logger();
    let mut errors = Vec::new();
    let statements = parse_Statements_str(&mut errors,
        "
        register xY {
            a : 32 = 0x1234;
        }
        x_a = 0x42;
        Stat = 0;
        pc = 0;
        ").unwrap();
    let program = Program::new_y86(statements).unwrap();
    let mut running_program = RunningProgram::new_y86(program);
    let mut options = RunOptions::default();
    options.set_debug();
    running_program.set_options(options);
    let mut result: Vec<u8> = Vec::new();
    running_program.step_with_output(&mut result).unwrap();
    let result_as_string = String::from_utf8_lossy(result.as_slice()).into_owned();
    debug!("result is {:?}", result_as_string);
    assert!(result_as_string.contains("Y_a                   0x00001234"));
    assert!(result_as_string.contains("x_a                   0x00000042"));
    assert!(result_as_string.contains("i10bytes  0x00000000000000000000"));
    assert!(!result_as_string.contains("stall_Y"));
}

#[test]
#[cfg(feature="require-mux-default")]
fn error_mux_default() {
    init_logger();
    let message = get_errors_for("
    wire foo : 1;
    foo = [
        pc == 42 : 100;
        pc > 42 : 99;
    ];
    Stat = 0;
    pc = 0;
    ");
    debug!("message is {:?}", message);
    assert!(message.contains("missing required default"));
}

#[test]
#[cfg(feature="disallow-multiple-mux-default")]
fn error_mux_two_defaults() {
    init_logger();
    let message = get_errors_for("
    wire foo : 1;
    foo = [
        REG_RSP: 100;
        1: 42;
    ];
    Stat = 0;
    pc = 0;
    ");
    debug!("message is {:?}", message);
    assert!(message.contains("multiple conditions which are always true"));
}



#[test]
fn suggest_capitalization_constant_decl() {
    init_logger();
    let message = get_errors_for("
        const Bar = le;
        Stat = 0;
        pc = 0;
    ");
    debug!("message is {:?}", message);
    assert!(message.contains("Did you mean 'LE'?"));
    assert!(!message.contains("fixed"));  // message should not mention fixed functionality
}

#[test]
fn suggest_capitalization_register_default() {
    init_logger();
    let message = get_errors_for("
        register xY {
            foo : 4 = nop;
        }
        Stat = 0;
        pc = 0;
    ");
    debug!("message is {:?}", message);
    assert!(message.contains("Did you mean 'NOP'?"));
    assert!(!message.contains("fixed"));  // message should not mention fixed functionality
}

#[test]
fn suggest_capitalization_assignment_constant() {
    init_logger();
    let message = get_errors_for("
        Stat = stat_aok;
        pc = 0;
    ");
    debug!("message is {:?}", message);
    assert!(message.contains("Did you mean 'STAT_AOK'?"));
    assert!(!message.contains("fixed"));  // message should not mention fixed functionality
}

#[test]
fn suggest_capitalization_assignment_constant_to_constant() {
    init_logger();
    let message = get_errors_for("
        const FOO = stat_aok;
        Stat = STAT_AOK;
        pc = 0;
    ");
    debug!("message is {:?}", message);
    assert!(message.contains("Did you mean 'STAT_AOK'?"));
    assert!(!message.contains("fixed"));  // message should not mention fixed functionality
}

#[test]
fn suggest_capitalization_assignment_wire() {
    init_logger();
    let message = get_errors_for("
        wire Foo : 4;
        Foo = 42;
        Stat = FOO;
        pc = 0;
    ");
    debug!("message is {:?}", message);
    assert!(message.contains("Did you mean 'Foo'?"));
}

#[test]
fn usage_and_assignment_of_undeclared_gives_both_errors() {
    init_logger();
    let message = get_errors_for("
        Foo = 42;
        Stat = STAT_AOK;
        pc = Foo;
    ");
    debug!("message is {:?}", message);
    assert!(message.contains("assigned value"));
    assert!(message.contains("in expression"));
    assert!(!message.contains("fixed"));  // message should not mention fixed functionality
}

#[test]
#[cfg(feature="disallow-unreachable-options")]
fn disallow_unreachable_mux_error() {
    init_logger();
    let message = get_errors_for("
        wire Foo: 32, bar: 32;
        Foo = [ bar > 32: 1; 1 : 2; bar < 32: 3 ];
        pc = 0;
        bar = i10bytes[0..32];
        Stat = STAT_AOK;
    ");
    debug!("message is {:?}", message);
    assert!(message.contains("has at least one case that will never be reached"));
}
