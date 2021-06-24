use std::collections::btree_map::BTreeMap;
use std::collections::HashSet;
use std::convert::From;
use std::error;
use std::fmt;
use std::io::Write;
use std::io;

use lalrpop_util::{ErrorRecovery, ParseError};

use ast::{SpannedExpr, MuxOption, WireWidth};
use lexer::{Tok, Loc, Span};
use io::FileContents;

#[derive(Debug)]
pub enum Error {
    MismatchedMuxWidths(Vec<MuxOption>, Vec<WireWidth>),
    MismatchedExprWidths(SpannedExpr, WireWidth, SpannedExpr, WireWidth),
    MismatchedWireWidths(String, WireWidth, SpannedExpr, WireWidth),
    // register bank, register name, expr
    MismatchedRegisterDefaultWidths {
        bank: String,
        register_name: String,
        register_width: WireWidth,
        default_expression: SpannedExpr,
        expression_width: WireWidth,
    },
    // FIXME: location of definitions?
    DuplicateRegister {
        bank: String,
        register_name: String,
    },
    RuntimeMismatchedWidths(),
    UndeclaredWireAssigned { name: String, span: Span, close_name: Option<String> },
    UndeclaredWireRead { name: String, expr: SpannedExpr, close_name: Option<String> },
    NonConstantWireRead(String, SpannedExpr),
    UnsetWire(String, Span),
    UnsetBuiltinWire(String),
    UnsetUndeclaredWire(String),
    UnsetRegisterInputWire { name: String, register_span: Span },
    RedeclaredWire(String, Span, Span),
    DoubleAssignedWire(String, Span, Span),
    DoubleAssignedRegisterWire {
        name: String,
        register_span: Span,
        assign_span: Span,
    },
    DoubleDeclaredRegisterOutWire {
        name: String,
        old_span: Span,
        new_span: Span
    },
    DoubleAssignedFixedOutWire(String, Span),
    RedeclaredBuiltinWire(String, Span),
    PartialFixedInput {
        found_input: String,
        all_inputs: Vec<Vec<String>>,
    },
    WireLoop(Vec<String>),
    InvalidWireWidth(Span),
    // FIXME: location
    InvalidRegisterBankName(String, Span),
    InvalidBitIndex(SpannedExpr, u8),
    NonBooleanWidth(SpannedExpr),
    NoBitWidth(SpannedExpr),
    MisorderedBitIndexes(SpannedExpr),
    InvalidConstant(Span),
    WireTooWide(SpannedExpr),
    ExpectedStatementFoundExpr(SpannedExpr),
    UnterminatedComment(Loc),
    LexicalError(Loc),
    InternalParserErrorNear(Span, String),
    MissingWireWidth(Span),
    WireAssignedInDeclaration(Span),
    MissingRegisterWidth(Span),
    AddedConstWidth(Span),
    MissingAssignmentMux(Span),
    RegisterDeclaredWithWire(Span),
    NoMuxDefaultOption(SpannedExpr),
    MultipleMuxDefaultOption(SpannedExpr),
    UnreachableOptions(SpannedExpr),
    EmptyFile(),
    UnparseableLine(String), // .yo input -- FIXME: rename
    InvalidToken(Loc),
    UnrecognizedToken { location: Span, expected: Vec<String> },
    ExtraToken(Span),
    MultipleErrors(Vec<Error>),
    IoError(io::Error),
    FmtError(fmt::Error),
}

/* utility function for producing error values */
pub fn find_close_names_in<'a, Iter: IntoIterator<Item=&'a str>>(target_name: &'a str, possible_names: Iter) -> Option<String> {
    debug!("find_close_names_in for {:?}", target_name);
    let mut result = None;
    for possible_name in possible_names {
        debug!("> {:?}", possible_name);
        if target_name.eq_ignore_ascii_case(possible_name) {
            result = Some(String::from(possible_name));
        }
    }
    return result;
}

fn error<W: Write>(output: &mut W, message: &str) -> Result<(), io::Error> {
    let mut first_line = true;
    for line in message.lines() {
        if first_line {
            write!(output, "error: {}\n", line)?;
            first_line = false;
        } else {
            write!(output, "       {}\n", line)?;
        }
    }
    Ok(())
}

fn error_continue<W: Write>(output: &mut W, message: &str) -> Result<(), io::Error> {
    for line in message.lines() {
        write!(output, "       {}\n", line)?;
    }
    Ok(())
}

fn s_are(i: usize) -> &'static str {
    if i != 1 {
        "s are"
    } else {
        " is"
    }
}

fn format_token_list(tokens: &Vec<String>) -> String {
    let all_compare_operators = vec!(
        "!=", "<", "<=", "==", ">", ">=", ">>",
    );
    let all_bin_operators = vec!(
        "&", "&&", "*", "+", "-", "/", "<<", "^", "|", "||", "in"
    );
    let all_un_operators = vec!(
        "!", "-", "~"
    );
    // deliberately omitted:
        // .. (wire concatenation, syntax requires parens)
        // []
        // ()
    debug!("format_token_list({:?})", tokens);
    let mut token_set: HashSet<String> = HashSet::new();
    for token in tokens {
        token_set.insert(token.clone());
    }
    let mut num_compare_operators = 0;
    for operator in &all_compare_operators {
        let quoted_operator = format!("\"{}\"", operator);
        if token_set.contains(&quoted_operator) {
            num_compare_operators += 1;
        }
    }
    let mut num_bin_operators = 0;
    for operator in &all_bin_operators {
        let quoted_operator = format!("\"{}\"", operator);
        if token_set.contains(&quoted_operator) {
            num_bin_operators += 1;
        }
    }
    let mut num_un_operators = 0;
    for operator in &all_un_operators {
        let quoted_operator = format!("\"{}\"", operator);
        if token_set.contains(&quoted_operator) {
            num_un_operators += 1;
        }
    }
    let mut found_list = Vec::new();
    if num_compare_operators == all_compare_operators.len() {
        found_list.push(String::from("a comparison operator"));
        for operator in &all_compare_operators {
            let quoted_operator = format!("\"{}\"", operator);
            token_set.remove(&quoted_operator);
        }
    }
    if num_bin_operators == all_bin_operators.len() {
        found_list.push(String::from("a binary operator"));
        for operator in &all_bin_operators {
            let quoted_operator = format!("\"{}\"", operator);
            token_set.remove(&quoted_operator);
        }
    }
    if num_un_operators == all_un_operators.len() {
        found_list.push(String::from("a unary operator"));
        for operator in &all_un_operators {
            let quoted_operator = format!("\"{}\"", operator);
            token_set.remove(&quoted_operator);
        }
    }
    for possible_token in token_set {
        match possible_token.as_str() {
            "ID" => found_list.push(String::from("an identifier (wire name)")),
            "CONSTANT" => found_list.push(String::from("an integer constant")),
            _ => {
                if &possible_token[0..1] == "\"" {
                    // replace double with single quotes
                    let new_token = format!("'{}'", &possible_token[1..(possible_token.len() - 1)]);
                    found_list.push(new_token);
                } else {
                    found_list.push(String::from(possible_token));
                }
            }
        }
    }
    found_list.sort();
    let mut formatted_list = String::new();
    if found_list.len() == 1 { 
        formatted_list.push_str(&found_list[0]);
    } else if found_list.len() == 2 {
        formatted_list.push_str(&found_list[0]);
        formatted_list.push_str(" or ");
        formatted_list.push_str(&found_list[1]);
    } else if let Some((format_last, format_rest)) = found_list.split_last() {
        for item in format_rest {
           formatted_list.push_str(&format!("{}, ", item));
        }
        formatted_list.push_str(&format!("or {}", format_last));
    }
    formatted_list
}

impl Error {
    pub fn format_for_contents<W: Write>(&self, output: &mut W, contents: &FileContents) -> Result<(), io::Error> {
        match *self {
            Error::MultipleErrors(ref vec) => {
                for item in vec {
                    item.format_for_contents(output, contents)?;
                }
            },
            Error::MismatchedMuxWidths(ref options, ref widths) => {
                error(output, "Mismatched wire widths for mux options.")?;
                let mut by_width = BTreeMap::new();
                for i in 0..options.len() {
                    let width = widths[i];
                    if width == WireWidth::Unlimited {
                        continue;
                    }
                    let ref option = options[i];
                    let lst = by_width.entry(width).or_insert(Vec::new());
                    lst.push(option)
                }
                for (width, lst) in by_width {
                    error_continue(output,
                                   &format!("{} option{} {} bits wide:\n",
                                            lst.len(), s_are(lst.len()), width.bits_or_128()))?;
                    for item in lst {
                        write!(output, "{}",
                               contents.show_region(item.value.span.0, item.value.span.1))?;
                    }
                }
            },
            Error::MismatchedExprWidths(ref first, first_width, ref second, second_width) => {
                error(output, &format!(
                    "Mismatched wire widths.\nOne side is {} bits wide:\n", first_width.bits_or_128()))?;
                write!(output, "{}", contents.show_region(first.span.0, first.span.1))?;
                error_continue(output, &format!(
                    "The other side is {} bits wide:\n", second_width.bits_or_128()))?;
                write!(output, "{}", contents.show_region(second.span.0, second.span.1))?;
            },
            Error::MismatchedWireWidths(ref name, first_width, ref second, second_width) => {
                error(output, &format!(
                    "Mismatched wire widths.\nThe wire '{}' is declared as {} bits wide.\n\
                     But a {} bit wide value is assigned to it:\n",
                    name, first_width.bits_or_128(), second_width.bits_or_128()))?;
                write!(output, "{}", contents.show_region(second.span.0, second.span.1))?;
            },
            Error::MismatchedRegisterDefaultWidths {
                ref bank, ref register_name, ref default_expression,
                ref register_width, ref expression_width
            } => {
                error(output, &format!(
                    "Register '{}' in bank '{}' is {} bits wide, but default value is \
                     {} bits wide:\n",
                     register_name, bank, register_width.bits_or_128(), expression_width.bits_or_128()))?;
                write!(output, "{}", contents.show_region(default_expression.span.0, default_expression.span.1))?;
            },
            // FIXME: show line numbers
            Error::DuplicateRegister { ref bank, ref register_name } => {
                error(output, &format!(
                    "Register '{}' in bank '{}' defined twice.", register_name, bank))?;
            },
            Error::RuntimeMismatchedWidths() => {
                error(output, &format!("Unexpected wire width disagreement."))?;
            },
            Error::UndeclaredWireAssigned { ref name, ref span, ref close_name } => {
                // TODO: suggestions for wire meant?
                error(output, &format!(
                            "Undeclared wire '{}' assigned value:",
                            name))?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
                match *close_name {
                    Some(ref other_name) => {
                        error_continue(output, &format!("(Did you mean '{}'?)", other_name))?;
                    },
                    None => {
                        if name.chars().count() > 2 && name.chars().nth(1) == Some('_') {
                            error_continue(output, &format!("(Missing register declaration?)"))?;
                        } else {
                            error_continue(output, &format!("(Did you mean to declare it with 'wire {}' or 'const {}'?)", name, name))?;
                        }
                    },
                }
            },
            Error::UndeclaredWireRead { ref name, ref expr, ref close_name } => {
                // TODO: suggestions for wire meant?
                error(output, &format!(
                            "Usage of undeclared wire '{}' in expression:",
                            name))?;
                write!(output, "{}", contents.show_region(expr.span.0, expr.span.1))?;
                match *close_name {
                    Some(ref other_name) => {
                        error_continue(output, &format!("(Did you mean '{}'?)", other_name))?;
                    },
                    None => {
                        if name.chars().count() > 2 && name.chars().nth(1) == Some('_') {
                            error_continue(output, &format!("(Missing register declaration?)"))?;
                        } else {
                            error_continue(output, &format!("(Did you mean to declare it with 'wire {}' or 'const {}'?)", name, name))?;
                        }
                    },
                }
            },
            Error::NonConstantWireRead(ref name, ref expr) => {
                // TODO: suggestions for wire meant?
                error(output, &format!(
                            "Usage of non-constant wire '{}' in initial or constant value:",
                            name))?;
                write!(output, "{}", contents.show_region(expr.span.0, expr.span.1))?;
            },
            Error::UnsetWire(ref name, ref span) => {
                error(output, &format!(
                            "Wire '{}' never assigned but defined here:",
                            name))?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
            },
            Error::UnsetBuiltinWire(ref name) => {
                error(output, &format!(
                            "Wire '{}' required by fixed functionality but never assigned.",
                            name))?;
            },
            Error::UnsetUndeclaredWire(ref name) => {
                // TODO: We should always get UndeclaredWireRead instead.
                error(output, &format!(
                            "Wire '{}' was read but never declared.",
                            name))?;
            },
            Error::UnsetRegisterInputWire { ref name, ref register_span } => {
                error(output, &format!(
                            "Wire '{}' never assigned, but is input to the register defined here:",
                            name))?;
                write!(output, "{}", contents.show_region(register_span.0, register_span.1))?;
            },
            Error::RedeclaredWire(ref name, ref new_span, ref old_span) => {
                error(output, &format!("Wire '{}' redeclared. Declared here:", name))?;
                write!(output, "{}", contents.show_region(new_span.0, new_span.1))?;
                error_continue(output, "After being declared here here:")?;
                write!(output, "{}", contents.show_region(old_span.0, old_span.1))?;
            },
            Error::DoubleAssignedWire(ref name, ref new_span, ref old_span) => {
                error(output, &format!("Wire '{}' assigned twice. Assigned here:", name))?;
                write!(output, "{}", contents.show_region(new_span.0, new_span.1))?;
                error_continue(output, "After being assigned here:")?;
                write!(output, "{}", contents.show_region(old_span.0, old_span.1))?;
            },
            Error::DoubleAssignedFixedOutWire(ref name, ref new_span) => {
                error(output, &format!("Wire '{}' is output for fixed functionality but is assigned here:", name))?;
                write!(output, "{}", contents.show_region(new_span.0, new_span.1))?;
            },
            Error::DoubleAssignedRegisterWire { ref name, ref register_span , ref assign_span } => {
                error(output, &format!("Wire '{}' is output of a register declared here:", name))?;
                write!(output, "{}", contents.show_region(register_span.0, register_span.1))?;
                error_continue(output, &format!("but wire '{}' is assigned directly here:", name))?;
                write!(output, "{}", contents.show_region(assign_span.0, assign_span.1))?;
            },
            Error::DoubleDeclaredRegisterOutWire { ref name, ref old_span, ref new_span } => {
                error(output, &format!("Wire '{}' used by register declared here:", name))?;
                write!(output, "{}", contents.show_region(old_span.0, old_span.1))?;
                error_continue(output, &format!("but would also be used by register declared here:"))?;
                write!(output, "{}", contents.show_region(new_span.0, new_span.1))?;
            },
            Error::RedeclaredBuiltinWire(ref name, ref new_span) => {
                error(output, &format!("Builtin wire '{}' redeclared here:", name))?;
                write!(output, "{}", contents.show_region(new_span.0, new_span.1))?;
            },
            Error::PartialFixedInput { ref found_input, ref all_inputs } => {
                // FIXME: error should identify missing input
                error(output, &format!("Wire '{}' set, but not the rest of this piece of fixed functionality.", found_input))?;
                for input_set in all_inputs.into_iter() {
                    let mut filtered_set: Vec<String> = input_set.into_iter().filter(|x| *x != found_input).cloned().collect();
                    filtered_set.sort();
                    let mut lst = String::from("");
                    if filtered_set.len() > 2 {
                        lst = filtered_set[0..filtered_set.len() - 1].join(", ");
                        lst.push_str(", and ");
                        lst.push_str(&filtered_set[filtered_set.len() - 1]);
                    } else if filtered_set.len() == 2 {
                        lst.push_str(&filtered_set[0]);
                        lst.push_str(" and ");
                        lst.push_str(&filtered_set[1]);
                    } else if filtered_set.len() == 1 {
                        lst.push_str(&filtered_set[0])
                    } else {
                        continue;
                    }
                    error_continue(output, &format!("(Did you mean to set {}?)", lst))?;
                }
            },
            Error::InvalidWireWidth(ref span) => {
                error(output, &format!("Invalid wire width specified."))?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
            },
            Error::InvalidRegisterBankName(ref name, ref span) => {
                error(output, &format!("Register bank name '{}' invalid.\nRegister bank names must be two characters.\n\
                                        The first character (input prefix) must be a lowercase letter.\n\
                                        The second character (output prefix) must be an uppercase lettter.",
                                        name))?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
            },
            // FIXME: expression width
            Error::InvalidBitIndex(ref expr, index) => {
                error(output, &format!("Bit index '{}' out of range for expression:", index))?;
                write!(output, "{}", contents.show_region(expr.span.0, expr.span.1))?;
            },
            Error::NonBooleanWidth(ref expr) => {
                error(output, &format!("Non-boolean value used with boolean operator:"))?;
                write!(output, "{}", contents.show_region(expr.span.0, expr.span.1))?;
            },
            Error::NoBitWidth(ref expr) => {
                error(output, &format!("Expression with unknown width used in bit concatenation:"))?;
                write!(output, "{}", contents.show_region(expr.span.0, expr.span.1))?;
            },
            Error::MisorderedBitIndexes(ref expr) => {
                error(output, "Bit selection expression selects less than 0 bits:")?;
                write!(output, "{}", contents.show_region(expr.span.0, expr.span.1))?;
            },
            Error::MissingWireWidth(ref span) => {
                error(output, "Wire declaration missing width:")?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
            },
            Error::WireAssignedInDeclaration(ref span) => {
                error(output, "Wire declaration must be separate from assignment:")?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
            },
            Error::MissingRegisterWidth(ref span) => {
                error(output, "Register declaration missing width:")?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
            },
            Error::AddedConstWidth(ref span) => {
                error(output, "Constant declaration has unsupported explicit width:")?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
            },
            Error::MissingAssignmentMux(ref span) => {
                error(output, "Syntax error; probably missing '=' after here:")?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
            },
            Error::RegisterDeclaredWithWire(ref span) => {
                error(output, "Syntax error; attempting to use 'wire' to declare registers in a register bank?:")?;
                error_continue(output, "(correct syntax is like 'register xY { register_name : width = default; }')")?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
            }
            Error::NoMuxDefaultOption(ref expr) => {
                error(output, "Mux (case expression) missing required default option (e.g. '1 : some_value;'):")?;
                write!(output, "{}", contents.show_region(expr.span.0, expr.span.1))?;
            },
            Error::MultipleMuxDefaultOption(ref expr) => {
                error(output, "Mux (case expression) has multiple conditions which are always true:")?;
                write!(output, "{}", contents.show_region(expr.span.0, expr.span.1))?;
                error_continue(output, "(using constants instead of the result of comparing wires to constants?)")?;
            }
            Error::UnreachableOptions(ref expr) => {
                error(output, "Mux (case expression) has at least one case that will never be reached:")?;
                write!(output, "{}", contents.show_region(expr.span.0, expr.span.1))?;
                error_continue(output, "(put cases after a default case?)")?;
            }
            Error::InvalidConstant(ref span) => {
                error(output, "Constant value is out of range:")?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
            },
            Error::WireTooWide(ref expr) => {
                error(output, "Expression would produce a value wider than supported (128 bits):")?;
                write!(output, "{}", contents.show_region(expr.span.0, expr.span.1))?;
            },
            Error::UnterminatedComment(start) => {
                error(output, "Unterminated comment starting here:")?;
                write!(output, "{}", contents.show_region(start, start + 2))?;
            },
            Error::LexicalError(start) | Error::InvalidToken(start) => {
                error(output, "Parse error here:")?;
                write!(output, "{}", contents.show_region(start, start + 1))?;
            },
            Error::EmptyFile() => {
                error(output, &format!("Empty input file."))?;
            },
            Error::UnparseableLine(ref line) => {
                error(output, &format!("Could not parse '{}' in .yo file.", line))?;
            },
            Error::UnrecognizedToken { ref location, ref expected } => {
                let token;
                if location.1 >= contents.data().len() {
                    token = "<end of file>";
                } else {
                    token = &contents.data()[location.0..location.1];
                }
                let expected_formatted = format_token_list(expected);
                error(output, &format!("Unexpected token '{}', expected {}:",
                    token, expected_formatted))?;
                // heuristic check for missing semicolon at EOL
                if expected.iter().find(|x| *x == "\";\"").is_some() {
                    debug!("has semicolon");
                    let (_, start, _) = contents.line_number_and_bounds(location.0);
                    let before: &str = &contents.data()[start..location.0];
                    debug!("prefix is {:?}", before);
                    if before.find(|x: char| !x.is_whitespace()).is_none() {
                        error_continue(output, "(Missing semicolon before this?)")?;
                    }
                }
                write!(output, "{}", contents.show_region(location.0, location.1))?;
                // FIXME: note about missing ; if at beginning of line and ; is one of expected.
            },
            Error::ExtraToken(span) => {
                let token = &contents.data()[span.0..span.1];
                error(output, &format!("Unexpected token '{}':", token))?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
            },
            Error::WireLoop(ref lst) => {
                error(output, &format!("Circular dependency detected:"))?;
                for i in 0..lst.len() {
                    // FIXME: show code snippets of dependency?
                    error_continue(output, &format!("  '{}' depends on '{}'{}",
                        &lst[(i+1)%lst.len()], &lst[i],
                        if i == lst.len() - 1 { "" } else { " and" }
                        ))?;
                }
            },
            Error::ExpectedStatementFoundExpr(ref expr) => {
                error(output, &format!("Found expression, expected assignment or declaration:"))?;
                write!(output, "{}", contents.show_region(expr.span.0, expr.span.1))?;
            },
            Error::InternalParserErrorNear(ref span, ref info) => {
                error(output, &format!("Internal parser error near or before here:"))?;
                write!(output, "{}", contents.show_region(span.0, span.1))?;
                error_continue(output, &format!("Syntax error, parser bug, or both.\nInternal info about error: {}", info))?;
            },
            _ => {
                error(output, &format!("{}", *self))?;
            }
        }
        Ok(())
    }
}

impl From<io::Error> for Error {
    fn from(io_error: io::Error) -> Self {
        Error::IoError(io_error)
    }
}

impl From<fmt::Error> for Error {
    fn from(io_error: fmt::Error) -> Self {
        Error::FmtError(io_error)
    }
}

type ParseErrorType<'input> = ParseError<usize, Tok<'input>, Error>;
impl<'input> From<ParseErrorType<'input>> for Error {
    fn from(parse_error: ParseErrorType<'input>) -> Self {
        match parse_error {
            ParseError::InvalidToken { location } => Error::InvalidToken(location),
            ParseError::UnrecognizedToken { token, expected } => {
                Error::UnrecognizedToken {
                    location: (token.0, token.2),
                    expected: expected,
                }
            },
            ParseError::UnrecognizedEOF { location, expected } => {
                Error::UnrecognizedToken {
                    location: (location, location+1),
                    expected: expected
                }
            },
            ParseError::ExtraToken { token } => Error::ExtraToken((token.0, token.2)),
            ParseError::User { error } => error,
        }
    }
}

type ErrorRecoveryType<'input> = ErrorRecovery<usize, Tok<'input>, Error>;
impl<'input> From<ErrorRecoveryType<'input>> for Error {
    fn from(error_recovery: ErrorRecoveryType<'input>) -> Self {
        Error::from(error_recovery.error)
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match *self {
            Error::MismatchedMuxWidths(_, _) => "mismatched mux option widths",
            Error::MismatchedExprWidths(_, _, _, _) => "mismatched widths in expression",
            Error::MismatchedWireWidths(_, _, _, _) => "mismatched width between assignment value and wire",
            Error::MismatchedRegisterDefaultWidths {..} => "mismatched width in default value for register",
            Error::DuplicateRegister {..} => "duplicate register in register bank",
            Error::RuntimeMismatchedWidths() => "mismatched width detected while evaluating expression",
            Error::UndeclaredWireAssigned {..} => "undeclared wire assigned",
            Error::UndeclaredWireRead {..} => "undeclared wire read",
            Error::NonConstantWireRead(_,_) => "non-constant wire read",
            Error::UnsetWire(_,_) => "wire defined but never assigned",
            Error::UnsetBuiltinWire(_) => "builtin wire required but never assigned",
            Error::UnsetUndeclaredWire(_) => "wire required but never declared",
            Error::UnsetRegisterInputWire {..} => "builtin wire required but never assigned",
            Error::DoubleAssignedWire(_,_,_) => "multiply assigned wire found",
            Error::DoubleAssignedFixedOutWire(_,_) => "wire assigned by fixed functionality also assigned manually",
            Error::DoubleAssignedRegisterWire {..} => "wire assigned by register also assigned manually",
            Error::DoubleDeclaredRegisterOutWire {..} => "multiply declared register out wire found",
            Error::RedeclaredWire(_,_,_) => "multiply defined wire found",
            Error::RedeclaredBuiltinWire(_,_) => "redefined wire from fixed functionality",
            Error::PartialFixedInput {..} => "part of fixed functionality set, but not all",
            Error::WireLoop(_) => "circular dependency between wires found",
            Error::InvalidWireWidth(_) => "wire width out of range",
            Error::InvalidRegisterBankName(_,_) => "invalid register bank name",
            Error::InvalidBitIndex(_, _) => "invalid bit index for bit-slicing",
            Error::InvalidConstant(_) => "constant is too big or small",
            Error::WireTooWide(_) => "wire would be wider than 128 bits",
            Error::NoBitWidth(_) => "expression has unknown bit width",
            Error::NonBooleanWidth(_) => "non-boolean operand to boolean operation",
            Error::MisorderedBitIndexes(_) => "misordered bit indexes in bitslice",
            Error::UnterminatedComment(_) => "unterminated /*-style comment",
            Error::ExpectedStatementFoundExpr(_) => "statement expected; found expression",
            Error::MissingWireWidth(_) => "wire declaration missing width",
            Error::WireAssignedInDeclaration(_) => "wire assigned in declaration",
            Error::MissingRegisterWidth(_) =>"register declaration missing width",
            Error::AddedConstWidth(_) =>"constant declaration has unsupported width",
            Error::MissingAssignmentMux(_) => "missing '=' before Mux, probably",
            Error::RegisterDeclaredWithWire(_) => "register declared with 'wire', probably",
            Error::NoMuxDefaultOption(_) => "no default option for mux",
            Error::MultipleMuxDefaultOption(_) => "multiple default option for mux",
            Error::UnreachableOptions(_) => "default case in middle of mux",
            Error::LexicalError(_) => "unrecognized token",
            Error::EmptyFile() => "empty input file",
            Error::UnparseableLine(_) => "unparseable line in input file",
            Error::InvalidToken(_) => "invalid token", // FIXME: difference between this/unrecognized
            Error::UnrecognizedToken {..} => "unrecognized token",
            Error::ExtraToken(_) => "extra token",
            Error::MultipleErrors(_) => "multiple errors",
            Error::IoError(_) => "an I/O error occurred",
            Error::FmtError(_) => "a formatting error occurred",
            Error::InternalParserErrorNear(_, _) => "internal parser error",
        }
    }

    fn cause(&self) -> Option<&dyn error::Error> {
        match *self {
            Error::IoError(ref err) => Some(err as &dyn error::Error),
            _ => None,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Error::IoError(ref e) => write!(f, "{}", e)?,
            &Error::FmtError(ref e) => write!(f, "{}", e)?,
            _ => write!(f, "{:?}", self)?,
        }
        Ok(())
    }
}
