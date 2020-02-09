use std::borrow::Cow;

use crate::impl_prelude::*;

use self::TokenKind::*;
pub struct Lexer<'a> {
    pub byte_pos: BytePos,
    pub line: u32,
    pub code: &'a [u8],
    peek: Token,
}

impl<'a> Lexer<'a> {
    pub fn new(code: &'a [u8]) -> Result<Self> {
        let cursor = Cursor::new(0, 1);

        // Insert dummy peek to avoid wrapping peek by Option,
        // and then find real peek.
        let dummy_peek = Token::new(TokenKind::Eof, Pos::from_cursor(cursor));
        let mut lexer = Self {
            byte_pos: 0,
            line: 1,
            code,
            peek: dummy_peek,
        };

        lexer.next_token()?;
        Ok(lexer)
    }

    /// Emit next token.
    pub fn next_token(&mut self) -> Result<Token> {
        let current_token = self.peek;
        self.peek = self.next_token_impl()?;

        Ok(current_token)
    }

    fn next_token_impl(&mut self) -> Result<Token> {
        if self.peek_char().is_none() {
            self.peek = self.eof();
            return Ok(self.peek);
        }

        let start = self.cursor();
        let token = match self.next_char().unwrap() {
            '+' => Token::new(Plus, Pos::from_cursor(start)),
            '-' => Token::new(Minus, Pos::from_cursor(start)),
            '*' => Token::new(Star, Pos::from_cursor(start)),
            '/' => Token::new(Slash, Pos::from_cursor(start)),
            '=' => Token::new(Eq_, Pos::from_cursor(start)),
            '(' => Token::new(LParen, Pos::from_cursor(start)),
            ')' => Token::new(RParen, Pos::from_cursor(start)),
            '[' => Token::new(LBracket, Pos::from_cursor(start)),
            ']' => Token::new(RBracket, Pos::from_cursor(start)),
            '{' => Token::new(LBrace, Pos::from_cursor(start)),
            '}' => Token::new(RBrace, Pos::from_cursor(start)),
            '.' => Token::new(Dot, Pos::from_cursor(start)),
            '&' => Token::new(And, Pos::from_cursor(start)),
            '|' => Token::new(Or, Pos::from_cursor(start)),
            ',' => Token::new(Comma, Pos::from_cursor(start)),
            ';' => Token::new(SemiColon, Pos::from_cursor(start)),
            ':' => {
                if let Some('=') = self.peek_char() {
                    self.next_char();
                    Token::new(ColonEq, Pos::new(start, self.cursor()))
                } else {
                    Token::new(Colon, Pos::from_cursor(start))
                }
            }
            '<' => {
                if let Some('=') = self.peek_char() {
                    self.next_char();
                    Token::new(Le, Pos::new(start, self.cursor()))
                } else if let Some('>') = self.peek_char() {
                    self.next_char();
                    Token::new(Ne, Pos::new(start, self.cursor()))
                } else {
                    Token::new(Lt, Pos::from_cursor(start))
                }
            }
            '>' => {
                if let Some('=') = self.peek_char() {
                    self.next_char();
                    Token::new(Ge, Pos::new(start, self.cursor()))
                } else {
                    Token::new(Gt, Pos::from_cursor(start))
                }
            }
            '\n' => {
                if let Some('\r') = self.peek_char() {
                    self.next_char();
                }
                self.line += 1;
                self.next_token_impl()?
            }
            '\r' => {
                if let Some('\n') = self.peek_char() {
                    self.next_char();
                }
                self.line += 1;
                self.next_token_impl()?
            }
            '"' => self.parse_litstr(start)?,
            c if c.is_whitespace() => self.next_token_impl()?,
            c if c.is_alphabetic() || c == '_' => self.parse_ident(start),
            c if c.is_numeric() => {
                if c == '0' {
                    self.parse_num(start, true)?
                } else {
                    self.parse_num(start, false)?
                }
            }
            c => {
                return Err(Error::new(
                    format!("Invalid character: {}", c).into(),
                    Pos::from_cursor(start),
                ))
            }
        };
        Ok(token)
    }

    /// Peek next token without proceeding cursor.
    pub fn peek_token(&self) -> Token {
        self.peek
    }

    fn parse_ident(&mut self, start: Cursor) -> Token {
        while let Some(c) = self.peek_char() {
            if c.is_alphanumeric() || c == '_' {
                self.next_char();
            } else {
                break;
            }
        }

        let kind = Ident(self.symbol_from(start.byte_pos, self.byte_pos));
        Token::new(kind, Pos::new(start, self.cursor()))
    }

    fn parse_num(&mut self, start: Cursor, start_with_zero: bool) -> Result<Token> {
        while let Some(c) = self.peek_char() {
            if c.is_numeric() && !start_with_zero {
                self.next_char();
            } else if c.is_numeric() {
                return Err(Error::new(
                    "Number must not start with zero".into(),
                    Pos::from_cursor(self.cursor()),
                ));
            } else {
                break;
            }
        }
        let kind = Num(self.symbol_from(start.byte_pos, self.byte_pos));
        Ok(Token::new(kind, Pos::new(start, self.cursor())))
    }

    fn parse_litstr(&mut self, start: Cursor) -> Result<Token> {
        let mut s = String::new();
        while let Some(c) = self.peek_char() {
            if c == '"' {
                self.next_char();
                s.push('\0');
                let kind = TokenKind::LitStr(Symbol::intern(&s));
                return Ok(Token::new(kind, Pos::new(start, self.cursor())));
            } else if c == '\\' {
                self.next_char();
                s.push_str(&self.parse_escape()?);
            } else {
                s.push(c);
                self.next_char();
            }
        }
        Err(Error::new(
            "Unterminated double quote string".into(),
            Pos::from_cursor(self.cursor()),
        ))
    }

    fn parse_escape(&mut self) -> Result<String> {
        if let Some(c) = self.next_char() {
            match c {
                'a' => Ok('\x07'.to_string()),
                'b' => Ok('\x08'.to_string()),
                'f' => Ok('\x0C'.to_string()),
                'n' => Ok('\x0A'.to_string()),
                'r' => Ok('\x0D'.to_string()),
                't' => Ok('\x09'.to_string()),
                'v' => Ok('\x0B'.to_string()),
                '"' => Ok('\x22'.to_string()),
                '\\' => Ok('\x5c'.to_string()),
                'x' => self.parse_litstr_radix(self.cursor(), 16),
                c if c.is_numeric() => {
                    self.byte_pos -= 1;
                    self.parse_litstr_radix(self.cursor(), 8)
                }
                c => {
                    self.byte_pos -= 1;
                    Err(Error::new(
                        format!("Invalid escape sequence: {}", c).into(),
                        Pos::from_cursor(self.cursor()),
                    ))
                }
            }
        } else {
            Err(Error::new(
                "Unterminated double quote string".into(),
                Pos::from_cursor(self.cursor()),
            ))
        }
    }

    /// Radix must be octal or hexadecimal.
    /// If radix is octal, number is must be composed of exact three characters.
    /// And when radix is hexadecimal, number is must be composed of exact two characters.
    fn parse_litstr_radix(&mut self, start: Cursor, radix: u32) -> Result<String> {
        if radix == 8 {
            self.byte_pos += 3;
        } else if radix == 16 {
            self.byte_pos += 2;
        } else {
            panic!();
        }

        if self.byte_pos > self.code.len() {
            return Err(Error::new(
                "Invalid escape number".into(),
                Pos::new(start, Cursor::new(self.code.len(), start.line)),
            ));
        }

        let number_as_string = self.slice_code(start.byte_pos, self.byte_pos);
        let number = u8::from_str_radix(number_as_string, radix).map_err(|_| {
            Error::new(
                format!("Invalid number {} is in string literal", number_as_string).into(),
                Pos::new(start, self.cursor()),
            )
        })?;

        Ok(number.to_string())
    }

    fn char_at(&self, at: BytePos) -> Option<char> {
        self.code.get(at).map(|b| *b as char)
    }

    fn slice_code(&self, start: BytePos, end: BytePos) -> &str {
        unsafe { std::str::from_utf8_unchecked(&self.code[start..end]) }
    }

    fn symbol_from(&self, start: BytePos, end: BytePos) -> Symbol {
        let ident_str = self.slice_code(start, end);
        Symbol::intern(ident_str)
    }

    fn cursor(&self) -> Cursor {
        Cursor::new(self.byte_pos, self.line)
    }

    fn next_char(&mut self) -> Option<char> {
        let c = self.char_at(self.byte_pos);
        self.byte_pos += 1;
        c
    }

    fn peek_char(&self) -> Option<char> {
        self.char_at(self.byte_pos)
    }

    fn eof(&self) -> Token {
        Token::new(Eof, Pos::from_cursor(self.cursor()))
    }
}

#[derive(Clone, Copy)]
pub struct Token {
    pub kind: TokenKind,
    pub pos: Pos,
}

impl Token {
    fn new(kind: TokenKind, pos: Pos) -> Self {
        Token { kind, pos }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TokenKind {
    Plus,
    Minus,
    Star,
    Slash,
    Eq_,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    ColonEq,
    Comma,
    Colon,
    SemiColon,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Dot,
    Eof,
    Ident(Symbol),
    Num(Symbol),
    LitStr(Symbol),
}

impl TokenKind {
    pub fn as_str(self) -> Cow<'static, str> {
        match self {
            Plus => "+".into(),
            Minus => "-".into(),
            Star => "*".into(),
            Slash => "/".into(),
            Eq_ => "=".into(),
            Ne => "<>".into(),
            Lt => "<".into(),
            Le => "<=".into(),
            Gt => ">".into(),
            Ge => ">=".into(),
            And => "&".into(),
            Or => "|".into(),
            ColonEq => ":=".into(),
            Comma => ",".into(),
            Colon => ":".into(),
            SemiColon => ";".into(),
            LParen => "(".into(),
            RParen => ")".into(),
            LBracket => "[".into(),
            RBracket => "]".into(),
            LBrace => "{".into(),
            RBrace => "}".into(),
            Dot => ".".into(),
            Eof => "EoF".into(),
            Ident(symbol) => symbol.as_str().into(),
            Num(symbol) => symbol.as_str().into(),
            LitStr(symbol) => format!(r#""{}""#, symbol.as_str()).into(),
        }
    }

    pub fn var(self) -> Option<Symbol> {
        match self {
            Ident(symbol) => {
                if symbol.is_kw() {
                    None
                } else {
                    Some(symbol)
                }
            }
            _ => None,
        }
    }

    pub fn num(self) -> Option<Symbol> {
        match self {
            Num(symbol) => Some(symbol),
            _ => None,
        }
    }

    pub fn litstr(self) -> Option<Symbol> {
        match self {
            LitStr(symbol) => Some(symbol),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex_single_char() {
        let code = "+-*/=()[]{}.&|,;".as_bytes();
        let mut lexer = Lexer::new(code).unwrap();
        assert_eq!(Plus, lexer.next_token().unwrap().kind);
        assert_eq!(Minus, lexer.next_token().unwrap().kind);
        assert_eq!(Star, lexer.next_token().unwrap().kind);
        assert_eq!(Slash, lexer.next_token().unwrap().kind);
        assert_eq!(Eq_, lexer.next_token().unwrap().kind);
        assert_eq!(LParen, lexer.next_token().unwrap().kind);
        assert_eq!(RParen, lexer.next_token().unwrap().kind);
        assert_eq!(LBracket, lexer.next_token().unwrap().kind);
        assert_eq!(RBracket, lexer.next_token().unwrap().kind);
        assert_eq!(LBrace, lexer.next_token().unwrap().kind);
        assert_eq!(RBrace, lexer.next_token().unwrap().kind);
        assert_eq!(Dot, lexer.next_token().unwrap().kind);
        assert_eq!(And, lexer.next_token().unwrap().kind);
        assert_eq!(Or, lexer.next_token().unwrap().kind);
        assert_eq!(Comma, lexer.next_token().unwrap().kind);
        assert_eq!(SemiColon, lexer.next_token().unwrap().kind);
        assert_eq!(Eof, lexer.next_token().unwrap().kind);
    }

    #[test]
    fn test_lex_multi_char() {
        let code = "<<=<>>>=::=".as_bytes();
        let mut lexer = Lexer::new(code).unwrap();
        assert_eq!(Lt, lexer.next_token().unwrap().kind);
        assert_eq!(Le, lexer.next_token().unwrap().kind);
        assert_eq!(Ne, lexer.next_token().unwrap().kind);
        assert_eq!(Gt, lexer.next_token().unwrap().kind);
        assert_eq!(Ge, lexer.next_token().unwrap().kind);
        assert_eq!(Colon, lexer.next_token().unwrap().kind);
        assert_eq!(ColonEq, lexer.next_token().unwrap().kind);
        assert_eq!(Eof, lexer.next_token().unwrap().kind);
    }

    #[test]
    fn test_ident() {
        let code = "Foo + _bar".as_bytes();
        let mut lexer = Lexer::new(code).unwrap();

        let var1 = Symbol::intern("Foo");
        let var2 = Symbol::intern("_bar");
        assert_eq!(Ident(var1), lexer.next_token().unwrap().kind);
        assert_eq!(Plus, lexer.next_token().unwrap().kind);
        assert_eq!(Ident(var2), lexer.next_token().unwrap().kind);
        assert_eq!(Eof, lexer.next_token().unwrap().kind);
    }

    #[test]
    fn test_num() {
        let code = "10 + 20".as_bytes();
        let mut lexer = Lexer::new(code).unwrap();
        let num1 = Symbol::intern("10");
        let num2 = Symbol::intern("20");
        assert_eq!(Num(num1), lexer.next_token().unwrap().kind);
        assert_eq!(Plus, lexer.next_token().unwrap().kind);
        assert_eq!(Num(num2), lexer.next_token().unwrap().kind);
        assert_eq!(Eof, lexer.next_token().unwrap().kind);
    }

    #[test]
    fn test_peek() {
        let code = "+ /".as_bytes();
        let mut lexer = Lexer::new(code).unwrap();
        assert_eq!(Plus, lexer.peek_token().kind);
        assert_eq!(Plus, lexer.peek_token().kind);
        assert_eq!(Plus, lexer.next_token().unwrap().kind);
        assert_eq!(Slash, lexer.peek_token().kind);
        assert_eq!(Slash, lexer.next_token().unwrap().kind);
        assert_eq!(Eof, lexer.next_token().unwrap().kind);
    }

    #[test]
    fn test_pos() {
        let code = "Foo + _bar".as_bytes();
        let mut lexer = Lexer::new(code).unwrap();
        let pos1 = Pos::new(Cursor::new(0, 1), Cursor::new(3, 1));
        let pos2 = Pos::new(Cursor::new(4, 1), Cursor::new(5, 1));
        let pos3 = Pos::new(Cursor::new(6, 1), Cursor::new(10, 1));
        let pos4 = Pos::new(Cursor::new(10, 1), Cursor::new(11, 1));
        assert_eq!(pos1, lexer.next_token().unwrap().pos);
        assert_eq!(pos2, lexer.next_token().unwrap().pos);
        assert_eq!(pos3, lexer.next_token().unwrap().pos);
        assert_eq!(pos4, lexer.next_token().unwrap().pos);
    }

    #[test]
    fn test_br_line() {
        let code = "+ \n + \r + \n\r + \r\n + ".as_bytes();
        let mut lexer = Lexer::new(code).unwrap();
        assert_eq!(1, lexer.next_token().unwrap().pos.start.line);
        assert_eq!(2, lexer.next_token().unwrap().pos.start.line);
        assert_eq!(3, lexer.next_token().unwrap().pos.start.line);
        assert_eq!(4, lexer.next_token().unwrap().pos.start.line);
        assert_eq!(5, lexer.next_token().unwrap().pos.start.line);
    }

    #[test]
    fn test_lit_str() {
        let litstr = Symbol::intern("TIGER COMPILER\0");
        let code = r#""TIGER COMPILER""#.as_bytes();
        let mut lexer = Lexer::new(code).unwrap();
        assert_eq!(LitStr(litstr), lexer.next_token().unwrap().kind);
    }

    #[test]
    fn test_lit_str_escaped() {
        let litstr = Symbol::intern("255 255\0");
        let code = r#""\xff \377""#.as_bytes();
        let mut lexer = Lexer::new(code).unwrap();
        assert_eq!(LitStr(litstr), lexer.next_token().unwrap().kind);
    }
}
