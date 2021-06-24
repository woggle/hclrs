use std::ops::{Deref, DerefMut};
use std::collections::hash_map::HashMap;
use std::collections::hash_set::HashSet;
use std::convert::From;
use std::fmt;
use std::fmt::{Display, LowerHex, Formatter};
use std::num::ParseIntError;
use std::str::FromStr;

use lexer::Span;
use errors::{find_close_names_in, Error};

// if true:
// *  require equality for non-bitwise, non-comparison binary ops; (otherwise, take maximum)
const STRICT_WIDTHS_BINARY: bool = cfg!(feature="strict-wire-widths-binary");
// *  require boolean arguments for &&, ||, etc.
const STRICT_WIDTHS_BOOLEAN: bool = cfg!(feature="strict-boolean-ops");
// *  require default options for MUXes
const REQUIRE_MUX_DEFAULT: bool = cfg!(feature="require-mux-default");
// *  disallow multiple default options for MUXes, which usually means using a constant instaed of comparing to it
const DISALLOW_MULTIPLE_MUX_DEFAULT: bool = cfg!(feature="disallow-multiple-mux-default");
// *  disallow options after a default option in muxes because those options will never be reached
const DISALLOW_UNREACHABLE_OPTIONS: bool = cfg!(feature="disallow-unreachable-options");


#[derive(Clone,Copy,Debug,Eq,PartialEq,PartialOrd,Ord)]
pub enum WireWidth {
    Bits(u8),
    Unlimited,
}

impl From<usize> for WireWidth {
    fn from(s: usize) -> Self { WireWidth::Bits(s as u8) }
}

impl From<i32> for WireWidth {
    fn from(s: i32) -> Self { WireWidth::Bits(s as u8) }
}

impl From<u8> for WireWidth {
    fn from(s: u8) -> Self { WireWidth::Bits(s) }
}

impl FromStr for WireWidth {
    type Err = ParseIntError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match u8::from_str(s) {
            Ok(s) => Ok(WireWidth::Bits(s)),
            Err(x) => Err(x)
        }
    }
}

impl WireWidth {
    pub fn bits_or_128(&self) -> u8 {
        match *self {
            WireWidth::Bits(x) => x,
            _ => 128,
        }
    }

    pub fn possibly_boolean(self) -> bool {
        self == WireWidth::Unlimited || self == WireWidth::Bits(1)
    }

    pub fn combine(self, other: WireWidth) -> Option<WireWidth> {
        match (self, other) {
            (WireWidth::Unlimited, _) => Some(other),
            (_, WireWidth::Unlimited) => Some(self),
            (WireWidth::Bits(s), WireWidth::Bits(t)) =>
                if s == t {
                    Some(self)
                } else {
                    None
                }
        }
    }

    pub fn max(self, other: WireWidth) -> WireWidth {
        match (self, other) {
            (WireWidth::Unlimited, _) => other,
            (_, WireWidth::Unlimited) => self,
            (WireWidth::Bits(s), WireWidth::Bits(t)) =>
                if s > t {
                    self
                } else {
                    other
                }
        }
    }

    pub fn combine_exprs(self, other: WireWidth, left_expr: &SpannedExpr, right_expr: &SpannedExpr) -> Result<WireWidth, Error> {
        match self.combine(other) {
            Some(width) => Ok(width),
            None => Err(Error::MismatchedExprWidths(left_expr.clone(), self, right_expr.clone(), other))
        }
    }

    pub fn combine_expr_and_wire(self, other: WireWidth, wire: &str, right_expr: &SpannedExpr) -> Result<WireWidth, Error> {
        match self.combine(other) {
            Some(width) => Ok(width),
            None => Err(Error::MismatchedWireWidths(String::from(wire), self, right_expr.clone(), other))
        }
    }

    pub fn mask(self) -> u128 {
        match self {
            WireWidth::Unlimited => !0,
            WireWidth::Bits(0) => 0,
            WireWidth::Bits(s) => ((!0) >> (128 - s)),
        }
    }
}

#[derive(Clone,Copy,Eq,PartialEq,Debug)]
pub struct WireValue {
    pub bits: u128,
    pub width: WireWidth
}

impl Display for WireValue {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.bits)
    }
}

impl LowerHex for WireValue {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:x}", self.bits)
    }
}

impl WireValue {
    pub fn true_value() -> WireValue {
        WireValue { bits: 1, width: WireWidth::Bits(1) }
    }

    pub fn false_value() -> WireValue {
        WireValue { bits: 0, width: WireWidth::Bits(1) }
    }

    pub fn new(v: u128) -> WireValue {
        WireValue { bits: v, width: WireWidth::Unlimited }
    }

    pub fn from_u64(v: u64) -> WireValue {
        WireValue { bits: v.into(), width: WireWidth::Unlimited }
    }

    pub fn from_binary(s: &str) -> WireValue {
        WireValue {
            bits: u128::from_str_radix(s, 2).unwrap(),
            width: WireWidth::Bits(s.len() as u8),
        }
    }

    pub fn from_decimal(s: &str) -> WireValue {
        WireValue {
            bits: u128::from_str_radix(s, 10).unwrap(),
            width: WireWidth::Unlimited,
        }
    }

    pub fn from_hexadecimal(s: &str) -> WireValue {
        WireValue {
            bits: u128::from_str_radix(s, 16).unwrap(),
            width: WireWidth::Unlimited,
        }
    }

    pub fn as_width(self, new_width: WireWidth) -> WireValue {
        WireValue { bits: self.bits & new_width.mask(), width: new_width }
    }

    pub fn op<F>(self, other: WireValue, f: F, new_width: WireWidth) -> WireValue
            where F: Fn(u128, u128) -> u128 {
        WireValue { bits: f(self.bits, other.bits) & new_width.mask(), width: new_width }
    }

    pub fn is_true(self) -> bool {
        self.bits > 0
    }
}

impl From<u64> for WireValue {
    fn from(x: u64) -> WireValue { WireValue::new(x.into()) }
}

#[derive(Debug,Eq,PartialEq,Clone,Copy)]
enum BinOpKind {
    BooleanCombine,
    BooleanFromEqualWidth,
    EqualWidth,
    EqualWidthWeak,
}

#[derive(Debug,Eq,PartialEq)]
pub struct WireDecl {
    pub name: String,
    pub width: WireWidth,
    pub span: Span,
}

impl WireDecl {
    pub fn synthetic(name: &str, bits: u8) -> Self {
        WireDecl {
            name: String::from(name),
            width: WireWidth::from(bits),
            span: (0, 0),
        }
    }
}

#[derive(Debug,Eq,PartialEq)]
pub struct ConstDecl {
    pub name: String,
    pub name_span: Span,
    pub value: SpannedExpr,
}

#[derive(Debug,Eq,PartialEq,Clone,Copy)]
pub enum BinOpCode {
    Add,
    Sub,
    Mul,
    Div,
    Or,
    Xor,
    And,
    Equal,
    NotEqual,
    LessEqual,
    GreaterEqual,
    Less,
    Greater,
    LogicalAnd,
    LogicalOr,
    LeftShift,
    RightShift,
    Error,
}

fn boolean_to_value(x: bool) -> u128 {
    if x { 1 } else { 0 }
}

impl BinOpCode {
    fn kind(self) -> BinOpKind {
        match self {
            BinOpCode::LogicalAnd => BinOpKind::BooleanCombine,
            BinOpCode::LogicalOr => BinOpKind::BooleanCombine,
            BinOpCode::Equal => BinOpKind::BooleanFromEqualWidth,
            BinOpCode::LessEqual => BinOpKind::BooleanFromEqualWidth,
            BinOpCode::GreaterEqual => BinOpKind::BooleanFromEqualWidth,
            BinOpCode::Less => BinOpKind::BooleanFromEqualWidth,
            BinOpCode::Greater => BinOpKind::BooleanFromEqualWidth,
            BinOpCode::NotEqual => BinOpKind::BooleanFromEqualWidth,

            BinOpCode::Add => BinOpKind::EqualWidthWeak,
            BinOpCode::Sub => BinOpKind::EqualWidthWeak,
            BinOpCode::Mul => BinOpKind::EqualWidthWeak,
            BinOpCode::Div => BinOpKind::EqualWidthWeak,

            _ => BinOpKind::EqualWidth,
        }
    }

    fn apply_raw(self, left: u128, right: u128) -> u128 {
        match self {
            BinOpCode::Add => left.wrapping_add(right),
            BinOpCode::Sub => left.wrapping_sub(right),
            BinOpCode::Mul => left.wrapping_mul(right),
            BinOpCode::Div => left.wrapping_div(right),  // FIXME: handle divide-by-zero
            BinOpCode::Or =>  left | right,
            BinOpCode::Xor => left ^ right,
            BinOpCode::And => left & right,
            BinOpCode::Equal => boolean_to_value(left == right),
            BinOpCode::NotEqual => boolean_to_value(left != right),
            BinOpCode::LessEqual => boolean_to_value(left <= right),
            BinOpCode::GreaterEqual => boolean_to_value(left >= right),
            BinOpCode::Less => boolean_to_value(left < right),
            BinOpCode::Greater => boolean_to_value(left > right),
            BinOpCode::LogicalAnd => boolean_to_value(
                left != 0 && right != 0
            ),  // FIXME: shortcircuit support?
            BinOpCode::LogicalOr =>  boolean_to_value(
                left != 0 || right != 0
            ),
            BinOpCode::LeftShift =>  match (
                    left.wrapping_shl(right as u32),
                    right >= 128
                ) {
                (_, true) => 0,
                (x, false) => x,
            },
            BinOpCode::RightShift => match (
                    left.wrapping_shr(right as u32),
                    right >= 128
                ) {
                (_, true) => 0,
                (x, false) => x,
            },
            BinOpCode::Error => panic!("unreported parse error"),
        }
    }

    fn apply(self, left: WireValue, right: WireValue) -> Result<WireValue, Error> {
        let final_width = match self.kind() {
            BinOpKind::EqualWidth =>
                match left.width.combine(right.width) {
                    Some(width) => width,
                    None => {
                        return Err(Error::RuntimeMismatchedWidths());
                    },
                },
            BinOpKind::EqualWidthWeak =>
                if STRICT_WIDTHS_BINARY {
                    match left.width.combine(right.width) {
                        Some(width) => width,
                        None => return Err(Error::RuntimeMismatchedWidths()),
                    }
                } else {
                    left.width.max(right.width)
                },
            BinOpKind::BooleanCombine | BinOpKind::BooleanFromEqualWidth =>
                WireWidth::Bits(1),
        };
        Ok(left.op(right, |l, r| self.apply_raw(l, r), final_width))
    }
}

#[derive(Debug,Eq,PartialEq,Copy,Clone)]
pub enum UnOpCode {
    Plus,
    Negate,
    Complement,
    Not,
}

impl UnOpCode {
    fn apply(self, value: WireValue) -> Result<WireValue, Error> {
        let new_value = match self {
            UnOpCode::Plus => value.bits,
            UnOpCode::Negate => !value.bits + 1,
            UnOpCode::Complement => !value.bits,
            UnOpCode::Not => if value.bits != 0 { 0 } else { 1 },
        };
        Ok(WireValue { bits: new_value & value.width.mask(),
                       width: if self == UnOpCode::Not { WireWidth::Bits(1) } else { value.width } })
    }
}

#[derive(Debug,Eq,PartialEq,Clone)]
pub struct MuxOption {
    pub condition: SpannedExpr,
    pub value: SpannedExpr,
}

#[derive(Debug,Eq,PartialEq,Clone)]
pub struct SpannedExpr {
    pub expr: Box<Expr>,
    pub span: Span,
}

impl SpannedExpr {
    pub fn new(span: Span, expr: Expr) -> Self {
        SpannedExpr {
            expr: Box::new(expr),
            span: span,
        }
    }

    pub fn to_expr(&self) -> &Expr { self.expr.as_ref() }

    pub fn to_mut_expr(&mut self) -> &mut Expr { self.expr.as_mut() }
}

impl Deref for SpannedExpr {
    type Target = Expr;

    fn deref(&self) -> &Expr { self.expr.as_ref() }
}

impl DerefMut for SpannedExpr {
    fn deref_mut(&mut self) -> &mut Expr { self.expr.as_mut() }
}

#[derive(Debug,Eq,PartialEq,Clone)]
pub enum Expr {
    Constant(WireValue),
    BinOp(BinOpCode, SpannedExpr, SpannedExpr),
    UnOp(UnOpCode, SpannedExpr),
    Mux(Vec<MuxOption>),
    NamedWire(String),
    BitSelect { from: SpannedExpr, low: u8, high: u8 },
    Concat(SpannedExpr, SpannedExpr),
    InSet(SpannedExpr, Vec<SpannedExpr>),
    Error,
}

pub type WireValues = HashMap<String, WireValue>;

impl SpannedExpr {
    pub fn get_width_and_check<'a>(&self, widths: &'a HashMap<&'a str, WireWidth>, constants: &WireValues) -> Result<WireWidth, Error> {
        match *self.expr {
            Expr::Constant(ref value) => Ok(value.width),
            Expr::BinOp(opcode, ref left, ref right) =>
                match opcode.kind() {
                    BinOpKind::EqualWidth => {
                        left.get_width_and_check(widths, constants)?.combine_exprs(right.get_width_and_check(widths, constants)?, left, right)
                    },
                    BinOpKind::EqualWidthWeak => {
                        if STRICT_WIDTHS_BINARY {
                            left.get_width_and_check(widths, constants)?.combine_exprs(right.get_width_and_check(widths, constants)?, left, right)
                        } else {
                            Ok((left.get_width_and_check(widths, constants)?).max(right.get_width_and_check(widths, constants)?))
                        }
                    },
                    BinOpKind::BooleanCombine => {
                        if STRICT_WIDTHS_BOOLEAN {
                            if !left.get_width_and_check(widths, constants)?.possibly_boolean() {
                                return Err(Error::NonBooleanWidth(left.clone()));
                            }
                            if !right.get_width_and_check(widths, constants)?.possibly_boolean() {
                                return Err(Error::NonBooleanWidth(right.clone()));
                            }
                        } else {
                            left.get_width_and_check(widths, constants)?;
                            right.get_width_and_check(widths, constants)?;
                        }
                        Ok(WireWidth::Bits(1))
                    },
                    BinOpKind::BooleanFromEqualWidth => {
                        left.get_width_and_check(widths, constants)?.combine_exprs(right.get_width_and_check(widths, constants)?, left, right)?;
                        Ok(WireWidth::Bits(1))
                    }
                },
            Expr::Mux(ref options) => {
                let mut maybe_width = Some(WireWidth::Unlimited);
                let mut all_widths = Vec::new();
                let mut seen_always_true = false;
                let mut seen_always_true_twice = false;
                let mut seen_unreachable_options = false; // to detect when there is a default in middle
                for option in options {
                    option.condition.get_width_and_check(widths, constants)?;
                    // if there is another option when seen_always_true has already been marked true
                    // then there is at least 1 unreachable option
                    if seen_always_true {
                        seen_unreachable_options = true;
                    }
                    if option.condition.always_true(&constants) {
                        if seen_always_true {
                            seen_always_true_twice = true;
                        }
                        seen_always_true = true;
                    }
                    let option_width = option.value.get_width_and_check(widths, constants)?;
                    all_widths.push(option_width);
                    if let Some(cur_width) = maybe_width {
                        maybe_width = cur_width.combine(option_width);
                    }
                }
                if REQUIRE_MUX_DEFAULT && !seen_always_true {
                    return Err(Error::NoMuxDefaultOption(self.clone()));
                }
                if DISALLOW_MULTIPLE_MUX_DEFAULT && seen_always_true_twice {
                    return Err(Error::MultipleMuxDefaultOption(self.clone()));
                }
                if DISALLOW_UNREACHABLE_OPTIONS && seen_unreachable_options { // should i include an option to turn this off?
                    return Err(Error::UnreachableOptions(self.clone()));
                }
                match maybe_width {
                    Some(width) => Ok(width),
                    None => Err(Error::MismatchedMuxWidths(options.clone(), all_widths))
                }
            },
            Expr::UnOp(UnOpCode::Not, ref covered) => {
                covered.get_width_and_check(widths, constants)?;
                Ok(WireWidth::Bits(1))
            },
            Expr::UnOp(_, ref covered) => covered.get_width_and_check(widths, constants),
            Expr::NamedWire(ref name) => match widths.get(name.as_str()) {
                Some(ref width) => Ok(**width),
                None => Err(Error::UndeclaredWireRead {
                    name: name.clone(), 
                    expr: self.clone(),
                    close_name: find_close_names_in(name, widths.keys().into_iter().cloned()),
                }),
            },
            Expr::BitSelect { ref from, low, high } => {
                if low > high {
                    return Err(Error::MisorderedBitIndexes(self.clone()));
                }
                match from.get_width_and_check(widths, constants)? {
                    WireWidth::Bits(inner_width) => {
                        if high > inner_width {
                            return Err(Error::InvalidBitIndex(self.clone(), high));
                        }
                    },
                    WireWidth::Unlimited => {},
                }
                Ok(WireWidth::Bits(high - low))
            }
            Expr::Concat(ref left, ref right) => {
                if let WireWidth::Bits(left_width) = left.get_width_and_check(widths, constants)? {
                    if let WireWidth::Bits(right_width) = right.get_width_and_check(widths, constants)? {
                        if left_width + right_width <= 128 {
                            Ok(WireWidth::Bits(left_width + right_width))
                        } else {
                            Err(Error::WireTooWide(self.clone()))
                        }
                    } else {
                        Err(Error::NoBitWidth(right.clone()))
                    }
                } else {
                    Err(Error::NoBitWidth(left.clone()))
                }
            },
            Expr::InSet(ref left, ref lst) => {
                let left_width = left.get_width_and_check(widths, constants)?;
                let mut errors = Vec::new();
                for item in lst {
                    let item_width = item.get_width_and_check(widths, constants)?;
                    match left_width.combine(item_width) {
                        Some(_) => {},
                        None => {
                            errors.push(Error::MismatchedExprWidths(left.clone(), left_width, item.clone(), item_width));
                        },
                    }
                }
                if errors.len() > 0 {
                    Err(Error::MultipleErrors(errors))
                } else {
                    Ok(WireWidth::Bits(1))
                }
            },
            /* panic since we should report error at parse-time instead */
            Expr::Error => panic!("expression did not parse correctly"),
        }
    }

    pub fn evaluate_constant(&self) -> Result<WireValue, Error> {
        self.evaluate(&WireValues::new())
    }

    pub fn evaluate<'a>(&self, wires: &'a WireValues) -> Result<WireValue, Error> {
        match *self.expr {
            Expr::Constant(value) => Ok(value),
            Expr::BinOp(opcode, ref left, ref right) => {
                let left_value = left.evaluate(wires)?;
                let right_value = right.evaluate(wires)?;
                opcode.apply(left_value, right_value)
            },
            Expr::UnOp(opcode, ref inner) => {
                let inner_value = inner.evaluate(wires)?;
                opcode.apply(inner_value)
            },
            Expr::Mux(ref options) => {
                let mut result: WireValue = WireValue::new(0);
                for ref option in options {
                    if option.condition.evaluate(wires)?.is_true() {
                        result = option.value.evaluate(wires)?;
                        break;
                    }
                }
                Ok(result)
            },
            Expr::NamedWire(ref name) => match wires.get(name) {
                Some(value) => Ok(*value),
                None => Err(Error::UndeclaredWireRead {
                    name: name.clone(),
                    expr: self.clone(),
                    close_name: find_close_names_in(name, wires.keys().into_iter().map(|x| x.as_str())),
                }),
            },
            Expr::BitSelect { ref from, low, high } => {
                let inner_value = from.evaluate(wires)?.bits;
                let shifted = inner_value >> low;
                Ok(WireValue::new(shifted).as_width(WireWidth::Bits(high - low)))
            },
            Expr::Concat(ref left, ref right) => {
                let left_value = left.evaluate(wires)?;
                let right_value = right.evaluate(wires)?;
                if let WireWidth::Bits(right_bits) = right_value.width {
                    if let WireWidth::Bits(left_bits) = left_value.width {
                        let shifted_left = left_value.bits << right_bits;
                        Ok(WireValue::new(shifted_left | right_value.bits).as_width(
                            WireWidth::Bits(left_bits + right_bits)))
                    } else {
                        Err(Error::NoBitWidth(left.clone()))
                    }
                } else {
                    Err(Error::NoBitWidth(right.clone()))
                }
            },
            Expr::InSet(ref left, ref lst) => {
                let left = left.evaluate(wires)?;
                for item in lst {
                    let right = item.evaluate(wires)?;
                    if left.bits == right.bits {
                        return Ok(WireValue::true_value());
                    }
                }
                Ok(WireValue::false_value())
            }
            /* panic since we should report error at parse-time instead */
            Expr::Error => panic!("expression did not parse correctly"),
        }
    }

    pub fn always_true<'a>(&self, values: &'a WireValues) -> bool {
        match self.evaluate(values) {
            Ok(value) => value.is_true(),
            Err(_) => false,
        }
    }

    pub fn apply_to_all<'a, 'b, F>(&'a self, func: &'b mut F) -> Result<(), Error>
            where F: FnMut(&'a Self) -> Result<(), Error> {
        func(self)?;
        match *self.expr {
            Expr::Constant(_) => {},
            Expr::BinOp(_, ref left, ref right) => {
                left.apply_to_all(func)?;
                right.apply_to_all(func)?;
            },
            Expr::UnOp(_, ref inner) => {
                inner.apply_to_all(func)?;
            },
            Expr::Mux(ref options) => {
                for ref option in options {
                    option.condition.apply_to_all(func)?;
                    option.value.apply_to_all(func)?;
                }
            },
            Expr::NamedWire(_) => {},
            Expr::BitSelect { ref from, .. } => {
                from.apply_to_all(func)?;
            },
            Expr::Concat(ref left, ref right) => {
                left.apply_to_all(func)?;
                right.apply_to_all(func)?;
            },
            Expr::InSet(ref left, ref lst) => {
                left.apply_to_all(func)?;
                for ref item in lst {
                    item.apply_to_all(func)?;
                }
            },
            Expr::Error => {},
        }
        Ok(())
    }

    pub fn apply_to_all_mut<F>(&mut self, func: &mut F) -> Result<(), Error>
            where F: FnMut(&mut Self) -> Result<(), Error> {
        func(self)?;
        match *self.expr {
            Expr::Constant(_) => {},
            Expr::BinOp(_, _, _) => {
                if let Expr::BinOp(_, ref mut left, _) = *self.expr {
                    left.apply_to_all_mut(func)?;
                } 
                if let Expr::BinOp(_, _, ref mut right) = *self.expr {
                    right.apply_to_all_mut(func)?;
                }
            },
            Expr::UnOp(_, ref mut inner) => {
                inner.apply_to_all_mut(func)?;
            },
            Expr::Mux(ref mut options) => {
                for ref mut option in options {
                    option.condition.apply_to_all_mut(func)?;
                    option.value.apply_to_all_mut(func)?;
                }
            },
            Expr::NamedWire(_) => {},
            Expr::BitSelect { ref mut from, .. } => {
                from.apply_to_all_mut(func)?;
            },
            Expr::Concat(_, _) => {
                if let Expr::Concat(ref mut left, _) = *self.expr {
                    left.apply_to_all_mut(func)?;
                } 
                if let Expr::Concat(_, ref mut right) = *self.expr {
                    right.apply_to_all_mut(func)?;
                }
            },
            Expr::InSet(_, _) => {
                if let Expr::InSet(ref mut left, _) = *self.expr {
                    left.apply_to_all_mut(func)?;
                }
                if let Expr::InSet(_, ref mut lst) = *self.expr {
                    for ref mut item in lst {
                        item.apply_to_all_mut(func)?;
                    }
                }
            },
            Expr::Error => {},
        }
        Ok(())
    }

    pub fn referenced_wires<'a>(&'a self) -> HashSet<&'a str> {
        let mut result = HashSet::new();
        self.apply_to_all(&mut |item| {
            match *item.expr {
                Expr::NamedWire(ref name) => {
                    result.insert(name.as_str());
                },
                _ => {},
            }
            Ok(())
        }).unwrap();
        result
    }

    pub fn find_references<'a>(&'a self, find_name: &str) -> Vec<SpannedExpr> {
        let mut result = Vec::new();
        self.apply_to_all(&mut |item| {
            match *item.expr {
                Expr::NamedWire(ref name) => {
                    if name == find_name {
                        result.push(item.clone());
                    }
                },
                _ => {},
            }
            Ok(())
        }).unwrap();
        result
    }
}

#[test]
fn referenced_wires() {
    let mut just_foo = HashSet::new();
    just_foo.insert("foo");
    let mut foo_and_bar = HashSet::new();
    foo_and_bar.insert("foo");
    foo_and_bar.insert("bar");
    assert_eq!(
        SpannedExpr::new((0, 0), Expr::NamedWire(String::from("foo"))).referenced_wires(),
        just_foo
    );
    assert_eq!(
        SpannedExpr::new((0, 0), Expr::UnOp(UnOpCode::Negate,
            SpannedExpr::new((0, 0), Expr::NamedWire(String::from("foo")))
        )).referenced_wires(),
        just_foo
    );
    assert_eq!(
        SpannedExpr::new((0, 0), Expr::BinOp(BinOpCode::Add,
            SpannedExpr::new((0, 0), Expr::NamedWire(String::from("foo"))),
            SpannedExpr::new((0, 0), Expr::NamedWire(String::from("bar")))
        )).referenced_wires(),
        foo_and_bar
    );
}

#[derive(Debug,Eq,PartialEq)]
pub struct Assignment {
    pub span: Span,
    pub names: Vec<(String, Span)>,
    pub value: SpannedExpr,
}

#[derive(Debug,Eq,PartialEq)]
pub struct RegisterDecl {
    pub span: Span,
    pub name: String,
    pub width: WireWidth,
    pub default: SpannedExpr,
}

#[derive(Debug,Eq,PartialEq)]
pub struct RegisterBankDecl {
    pub span: Span,
    pub name: String,
    pub name_span: Span,
    pub registers: Vec<RegisterDecl>,
}

#[derive(Debug,Eq,PartialEq)]
pub enum Statement {
    ConstDecls(Vec<ConstDecl>),
    WireDecls(Vec<WireDecl>),
    Assignments(Vec<Assignment>),
    RegisterBankDecl(RegisterBankDecl),
    Error,
}
