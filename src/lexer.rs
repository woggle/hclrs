use ast::{WireValue, WireWidth};
use std::cell::RefCell;
use std::str::CharIndices;

use errors::Error;
use io::FileContents;

pub type Spanned<T, E> = Result<(usize, T, usize), E>;

pub type Loc = usize;
pub type Span = (Loc, Loc);

/* nasty more information about panic hack */
thread_local! {
    pub static LAST_LOC : RefCell<Loc> = RefCell::new(0);
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum Tok<'input> {
    AndAnd, OrOr,
    Equal, NotEqual, GreaterEqual, Greater, LessEqual, Less,
    Assign,
    RightShift, LeftShift,
    Comma, Semicolon,
    Plus, Minus, And, Or, Xor, Times, Divide, Not,
    Constant(WireValue),
    OpenParen, CloseParen, OpenBrace, CloseBrace, OpenBracket, CloseBracket,
    Colon,
    Complement,
    DotDot,
    Wire,
    Const,
    Register,
    In,
    Identifier(&'input str),
}

pub struct Lexer<'input> {
    input: &'input str,
    chars: CharIndices<'input>,
    pending: Option<(usize, char)>,
    last: Option<(usize, char)>,
}

impl<'input> Lexer<'input> {
    pub fn new_for_file(input: &'input FileContents) -> Self {
        Lexer::new(input.data())
    }

    pub fn new(input: &'input str) -> Self {
        Lexer { input: input, chars: input.char_indices(), pending: None, last: None }
    }

    fn internal_next(&mut self) -> Option<(usize, char)> {
        match self.pending {
            Some(_) => {
                debug!("next from unget");
                self.last = self.pending;
                self.pending = None;
            },
            None => {
                self.last = self.chars.next()
            }
        }
        if let Some((new_loc, _)) = self.last {
            LAST_LOC.with(|loc| { *loc.borrow_mut() = new_loc });
        }
        assert_eq!(self.pending, None);
        debug!("next is {:?}", self.last);
        self.last
    }

    fn unget(&mut self) {
        debug!("unget");
        assert!(self.last.is_some());
        assert!(self.pending.is_none());
        self.pending = self.last;
        self.last = None;
    }


    fn peek_char(&mut self) -> Option<char> {
        if let Some((_, c)) = self.internal_next() {
            debug!("peeked at {:?}", c);
            self.unget();
            Some(c)
        } else {
            None
        }
    }

    fn choose_token(&mut self, start: usize, default: Tok<'static>, options: &[(char, Tok<'static>)]) ->  
            Spanned<Tok<'input>, Error> {
        let peeked = self.peek_char();
        for option in options {
            if Some(option.0) == peeked {
                debug!("token {:?}", option.1);
                self.internal_next();
                return Ok((start, option.1, start + 2))
            }
        }
        debug!("token {:?}", default);
        Ok((start, default, start + 1))
    }

    fn extract(&self, start: usize, end: usize) -> &'input str {
        return &self.input[start..end];
    }

    fn get_while<F>(&mut self, start: usize, f: F) -> (usize, &'input str, usize) where F: Fn(char) -> bool {
        // default to EOF
        let mut last = self.input.len();
        while let Some((i, c)) = self.internal_next() {
            if f(c) {
                // do nothing
            } else {
                last = i;
                self.unget();
                break;
            }
        }
        (start, self.extract(start, last), last)
    }

    fn expect_or_error<F>(&mut self, f: F) -> Result<char, Error> where F: Fn(char) -> bool {
        if let Some((i, c))  = self.internal_next() {
            if f(c) {
                Ok(c)
            } else {
                Err(Error::LexicalError(i))
            }
        } else {
            Err(Error::LexicalError(usize::max_value()))
        }
    }

    fn expect_peek_not<F>(&mut self, f: F) -> Result<(), Error> where F: Fn(char) -> bool {
        if let Some((i, c))  = self.internal_next() {
            if f(c) {
                Err(Error::LexicalError(i))
            } else {
                self.unget();
                Ok(())
            }
        } else {
            Ok(())
        }
    }

    fn handle_constant(&mut self, i: usize) -> Spanned<Tok<'input>, Error> {
        if let Some((_, c2)) = self.internal_next() {
            match c2 {
                'x' => {
                    self.expect_or_error(is_hexadecimal_char)?;
                    let (start_noprefix, hex, end) = self.get_while(i + 2, is_hexadecimal_char);
                    let start = start_noprefix - 2;
                    match u128::from_str_radix(&hex, 16) {
                        Ok(value) => {
                            return Ok((start, Tok::Constant(WireValue::new(value)), end));
                        }
                        Err(_) => {
                            return Err(Error::InvalidConstant((start, end)));
                        }
                    }
                },
                'b' => {
                    self.expect_or_error(is_binary_char)?;
                    let (start_noprefix, bin, end) = self.get_while(i + 2, is_binary_char);
                    let start = start_noprefix - 2;
                    self.expect_peek_not(is_decimal_char)?; // disallow 0b010112
                    match u128::from_str_radix(&bin, 2) {
                        Ok(value) => {
                            let width = WireWidth::Bits(bin.len() as u8);
                            return Ok((start, Tok::Constant(WireValue::new(value).as_width(width)), end));
                        }
                        Err(_) => {
                            return Err(Error::InvalidConstant((start, end)));
                        }
                    }
                }
                '0' ..= '9' => {
                    self.unget();
                    let (start, num, end) = self.get_while(i, is_decimal_char);
                    match u128::from_str_radix(&num, 10) {
                        Ok(value) => {
                            return Ok((start, Tok::Constant(WireValue::new(value)), end));
                        }
                        Err(_) => {
                            return Err(Error::InvalidConstant((start, end)));
                        }
                    }
                },
                _ => {
                    self.unget();
                    let start = i;
                    let end = i + 1;
                    let num = self.extract(start, end);
                    match u128::from_str_radix(&num, 10) {
                        Ok(value) => {
                            return Ok((start, Tok::Constant(WireValue::new(value)), end));
                        }
                        Err(_) => {
                            return Err(Error::InvalidConstant((start, end)));
                        }
                    }
                },
            }
        } else {
            let start = i;
            let end = i + 1;
            let num = self.extract(start, end);
            match u128::from_str_radix(&num, 10) {
                Ok(value) => {
                    return Ok((start, Tok::Constant(WireValue::new(value)), end));
                }
                Err(_) => {
                    return Err(Error::InvalidConstant((start, end)));
                }
            }
        }
    }

    fn resolve_identifier(&self, start: Loc, end: Loc) -> Tok<'input> {
        let name = self.extract(start, end);
        match name {
            "wire" => Tok::Wire,
            "const" => Tok::Const,
            "register" => Tok::Register,
            "in" => Tok::In,
            _ => Tok::Identifier(name),
        }
    }
}

fn is_identifier_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn is_start_identifier_char(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_hexadecimal_char(c: char) -> bool {
    (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')  || (c >= 'A' && c <= 'F')
}

fn is_decimal_char(c: char) -> bool {
    c >= '0' && c <= '9'
}

fn is_binary_char(c: char) -> bool {
    c >= '0' && c <= '1'
}

fn is_not_newline(c: char) -> bool {
    c != '\n' && c != '\r'
}

fn is_not_star(c: char) -> bool {
    c != '*'
}

fn simple_token<'input>(i: usize, t: Tok<'input>) -> Spanned<Tok<'input>, Error> {
    debug!("simple token {:?}", t);
    Ok((i, t, i + 1))
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Spanned<Tok<'input>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((i, c)) = self.internal_next() {
                debug!("read {:?}", (i, c));
                if c.is_whitespace() {
                    debug!("skip whitespace");
                    continue;
                } else if is_start_identifier_char(c) {
                    debug!("identifier?");
                    let (start, _, end) = self.get_while(i, is_identifier_char);
                    let the_token = self.resolve_identifier(start, end);
                    return Some(Ok((start, the_token, end)));
                } else if c >= '0' && c <= '9' {
                    debug!("integer constant");
                    return Some(self.handle_constant(i));
                } else {
                    let result = match c {
                        '#' => { // comment
                            debug!("# comment");
                            self.get_while(i, is_not_newline);
                            continue;
                        },
                        '/' => {
                            let c2 = self.peek_char();
                            if c2 == Some('/') { // //-style comment
                                debug!("// comment");
                                self.get_while(i, is_not_newline);
                                continue;
                            } else if c2 == Some('*') { // /*-style comment
                                debug!("/* comment");
                                let mut found_end = false;
                                loop {
                                    self.get_while(i, is_not_star);
                                    if self.peek_char() == Some('*') {
                                        self.internal_next();
                                        if self.peek_char() == Some('/') {
                                            found_end = true;
                                            self.internal_next();
                                            break;
                                        }
                                    } else if self.peek_char() == None {
                                        break
                                    }
                                }
                                if !found_end {
                                    return Some(Err(Error::UnterminatedComment(i)));
                                }
                                continue;
                            } else {
                                simple_token(i, Tok::Divide)
                            }
                        },
                        '&' => self.choose_token(i, Tok::And, &[('&', Tok::AndAnd)]),
                        '|' => self.choose_token(i, Tok::Or, &[('|', Tok::OrOr)]),
                        '=' => self.choose_token(i, Tok::Assign, &[('=', Tok::Equal)]),
                        '>' => self.choose_token(i, Tok::Greater, &[('>', Tok::RightShift), ('=', Tok::GreaterEqual)]),
                        '<' => self.choose_token(i, Tok::Less, &[('<', Tok::LeftShift), ('=', Tok::LessEqual)]),
                        '!' => self.choose_token(i, Tok::Not, &[('=', Tok::NotEqual)]),
                        ':' => simple_token(i, Tok::Colon),
                        '~' => simple_token(i, Tok::Complement),
                        ',' => simple_token(i, Tok::Comma),
                        ';' => simple_token(i, Tok::Semicolon),
                        '.' => {
                            if self.peek_char() == Some('.') {
                                self.internal_next();
                                debug!("token: ..");
                                Ok((i, Tok::DotDot, i + 2))
                            } else {
                                debug!("lexical error from ._");
                                Err(Error::LexicalError(i))
                            }
                        },
                        '+' => simple_token(i, Tok::Plus),
                        '-' => simple_token(i, Tok::Minus),
                        '^' => simple_token(i, Tok::Xor),
                        '*' => simple_token(i, Tok::Times),
                        '(' => simple_token(i, Tok::OpenParen),
                        ')' => simple_token(i, Tok::CloseParen),
                        '[' => simple_token(i, Tok::OpenBracket),
                        ']' => simple_token(i, Tok::CloseBracket),
                        '{' => simple_token(i, Tok::OpenBrace),
                        '}' => simple_token(i, Tok::CloseBrace),
                        _ => {
                            debug!("lexical error from unknown character");
                            Err(Error::LexicalError(i))
                        },
                    };
                    return Some(result);
                }
            } else {
                return None;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unicode_comment() {
        let mut lexer = Lexer::new("#❤️\nconst\n");
        assert_eq!(lexer.next().unwrap().unwrap().1, Tok::Const);
    }


    #[test]
    fn cr_newline() {
        let mut lexer = Lexer::new("#❤️\rconst\r");
        assert_eq!(lexer.next().unwrap().unwrap().1, Tok::Const);
    }

    #[test]
    fn eof_comment() {
        let mut lexer = Lexer::new("/* foo */");
        assert!(lexer.next().is_none());
    }

    #[test]
    fn unterminated_comment() {
        let mut lexer = Lexer::new("/* foo");
        if let Some(Err(Error::UnterminatedComment(loc))) = lexer.next() {
            assert_eq!(loc, 0);
        } else {
            assert!(false);
        }
    }
}
