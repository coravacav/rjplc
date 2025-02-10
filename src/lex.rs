use std::fmt::Write;

use anyhow::{bail, Result};

use crate::{measure, CustomDisplay};
#[cfg(test)]
use crate::{test_correct, test_solos};

#[repr(usize)]
#[derive(Debug, Clone, Copy, PartialEq)]
#[allow(non_camel_case_types, clippy::upper_case_acronyms)]
pub enum TokenType {
    ARRAY,
    ASSERT,
    BOOL,
    COLON,
    COMMA,
    DOT,
    ELSE,
    END_OF_FILE,
    EQUALS,
    FALSE,
    FLOAT,
    FLOATVAL,
    FN,
    IF,
    IMAGE,
    INT,
    INTVAL,
    LCURLY,
    LET,
    LPAREN,
    LSQUARE,
    NEWLINE,
    // Inlined Ops
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Not,
    Neq,
    Eq,
    Greater,
    Less,
    And,
    Or,
    GreaterEq,
    LessEq,
    //
    PRINT,
    RCURLY,
    READ,
    RETURN,
    RPAREN,
    RSQUARE,
    SHOW,
    STRING,
    STRUCT,
    SUM,
    THEN,
    TIME,
    TO,
    TRUE,
    VARIABLE,
    VOID,
    WRITE,
    TYPE,
}

#[derive(Clone, Copy)]
pub union Token {
    token: TokenType,
    index: usize,
}

impl Token {
    const SAFEBITS: u32 = 6;
    const DELETE_INDEX_SHIFT: u32 = usize::BITS - Self::SAFEBITS;

    fn new(token: TokenType) -> Self {
        Token { token }
    }

    #[must_use]
    pub const fn get_type(&self) -> TokenType {
        unsafe {
            std::mem::transmute::<usize, TokenType>(
                self.index << Self::DELETE_INDEX_SHIFT >> Self::DELETE_INDEX_SHIFT,
            )
        }
    }

    #[must_use]
    #[allow(clippy::missing_panics_doc)]
    pub fn get_index(&self) -> usize {
        #[cfg(debug_assertions)]
        {
            match self.get_type() {
                TokenType::VARIABLE
                | TokenType::STRING
                | TokenType::FLOATVAL
                | TokenType::INTVAL => {}
                t => panic!("Cannot access index of enum with type {t:?}"),
            }
        }

        // less than 64 variants so we just drop those :)
        unsafe { self.index >> Self::SAFEBITS }
    }

    #[allow(clippy::missing_panics_doc)]
    fn set_index(mut self, index: usize) -> Self {
        #[cfg(debug_assertions)]
        {
            match self.get_type() {
                TokenType::VARIABLE
                | TokenType::STRING
                | TokenType::FLOATVAL
                | TokenType::INTVAL => {}
                t => panic!("Cannot set index of enum with {t:?}"),
            }
        }

        let ty = unsafe { self.index } << Self::DELETE_INDEX_SHIFT >> Self::DELETE_INDEX_SHIFT;

        self.index = index
            .checked_shl(Self::SAFEBITS)
            .expect("You're compiling too big a file, please don't :)");

        // Restore discriminant
        unsafe {
            self.index |= ty;
        }

        self
    }
}

impl From<TokenType> for Token {
    fn from(token: TokenType) -> Self {
        Token { token }
    }
}

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.get_type())
    }
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        // This compares both at once.
        unsafe { self.index == other.index }
    }
}

impl CustomDisplay for Token {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match self.get_type() {
            TokenType::ARRAY => f.write_str("ARRAY 'array'"),
            TokenType::ASSERT => f.write_str("ASSERT 'assert'"),
            TokenType::BOOL => f.write_str("BOOL 'bool'"),
            TokenType::COLON => f.write_str("COLON ':'"),
            TokenType::COMMA => f.write_str("COMMA ','"),
            TokenType::DOT => f.write_str("DOT '.'"),
            TokenType::ELSE => f.write_str("ELSE 'else'"),
            TokenType::END_OF_FILE => f.write_str("END_OF_FILE"),
            TokenType::EQUALS => f.write_str("EQUALS '='"),
            TokenType::FALSE => f.write_str("FALSE 'false'"),
            TokenType::FLOAT => f.write_str("FLOAT 'float'"),
            TokenType::FN => f.write_str("FN 'fn'"),
            TokenType::IF => f.write_str("IF 'if'"),
            TokenType::IMAGE => f.write_str("IMAGE 'image'"),
            TokenType::INT => f.write_str("INT 'int'"),
            TokenType::LCURLY => f.write_str("LCURLY '{'"),
            TokenType::LET => f.write_str("LET 'let'"),
            TokenType::LPAREN => f.write_str("LPAREN '('"),
            TokenType::LSQUARE => f.write_str("LSQUARE '['"),
            TokenType::NEWLINE => f.write_str("NEWLINE"),
            TokenType::PRINT => f.write_str("PRINT 'print'"),
            TokenType::RCURLY => f.write_str("RCURLY '}'"),
            TokenType::READ => f.write_str("READ 'read'"),
            TokenType::RETURN => f.write_str("RETURN 'return'"),
            TokenType::RPAREN => f.write_str("RPAREN ')'"),
            TokenType::RSQUARE => f.write_str("RSQUARE ']'"),
            TokenType::SHOW => f.write_str("SHOW 'show'"),
            TokenType::STRUCT => f.write_str("STRUCT 'struct'"),
            TokenType::SUM => f.write_str("SUM 'sum'"),
            TokenType::THEN => f.write_str("THEN 'then'"),
            TokenType::TIME => f.write_str("TIME 'time'"),
            TokenType::TO => f.write_str("TO 'to'"),
            TokenType::TRUE => f.write_str("TRUE 'true'"),
            TokenType::VOID => f.write_str("VOID 'void'"),
            TokenType::WRITE => f.write_str("WRITE 'write'"),
            TokenType::TYPE => f.write_str("TYPE 'type'"),
            TokenType::VARIABLE => write!(f, "VARIABLE '{}'", string_map[self.get_index()]),
            TokenType::STRING => write!(f, "STRING '\"{}\"'", string_map[self.get_index()]),
            TokenType::FLOATVAL => write!(f, "FLOATVAL '{}'", string_map[self.get_index()]),
            TokenType::INTVAL => write!(f, "INTVAL '{}'", string_map[self.get_index()]),
            TokenType::Add => f.write_str("OP '+'"),
            TokenType::Sub => f.write_str("OP '-'"),
            TokenType::Mul => f.write_str("OP '*'"),
            TokenType::Div => f.write_str("OP '/'"),
            TokenType::Mod => f.write_str("OP '%'"),
            TokenType::Not => f.write_str("OP '!'"),
            TokenType::Greater => f.write_str("OP '>'"),
            TokenType::Less => f.write_str("OP '<'"),
            TokenType::Eq => f.write_str("OP '=='"),
            TokenType::Neq => f.write_str("OP '!='"),
            TokenType::And => f.write_str("OP '&&'"),
            TokenType::Or => f.write_str("OP '||'"),
            TokenType::GreaterEq => f.write_str("OP '>='"),
            TokenType::LessEq => f.write_str("OP '<='"),
        }
    }
}

/// # Errors
/// Failed to lex.
#[allow(clippy::too_many_lines)]
#[allow(clippy::range_plus_one)]
pub fn lex(str_input: &str) -> Result<(Vec<Token>, Vec<&str>)> {
    measure!("lex");
    let mut tokens: Vec<Token> = vec![];
    let mut string_map: Vec<&str> = vec![];

    let input = str_input.as_bytes();
    let mut index = 0;

    #[cfg(test)]
    let mut last_loop_index;

    loop {
        #[cfg(test)]
        {
            last_loop_index = index;
        }
        match input.get(index) {
            None => break tokens.push(TokenType::END_OF_FILE.into()),
            Some(b' ') => index += 1,
            Some(b'\\') => {
                if let Some(b'\n') = input.get(index + 1) {
                    index += 2;
                } else {
                    bail!("newline found in string literal");
                }
            }
            Some(b'/') => match input.get(index + 1) {
                Some(b'*') => {
                    let mut current_index = index + 2;
                    loop {
                        match input.get(current_index) {
                            Some(b'*') => {
                                if let Some(b'/') = input.get(current_index + 1) {
                                    break;
                                }

                                current_index += 1;
                            }
                            Some(10 | 32..=126) => current_index += 1,
                            Some(c) => {
                                bail!("illegal character {c:?} while lexing a block comment")
                            }
                            None => bail!("unterminated block comment"),
                        }
                    }
                    index = current_index + 2;
                }
                Some(b'/') => {
                    let mut current_index = index + 2;
                    loop {
                        match input.get(current_index) {
                            Some(b'\n') => break,
                            Some(32..=126) => current_index += 1,
                            Some(c) => {
                                bail!("illegal character {c:?} while lexing a line comment")
                            }
                            None => bail!("unterminated line comment"),
                        }
                    }
                    // include the newline
                    current_index += 1;

                    if tokens.last().map(Token::get_type) != Some(TokenType::NEWLINE) {
                        tokens.push(TokenType::NEWLINE.into());
                    }

                    index = current_index;
                }
                _ => {
                    tokens.push(TokenType::Div.into());
                    index += 1;
                }
            },
            Some(b'0'..=b'9') => {
                let mut current_index = index + 1;
                let mut is_float = false;
                loop {
                    match input.get(current_index) {
                        Some(b'.') => {
                            if is_float {
                                break;
                            }
                            is_float = true;
                            current_index += 1;
                        }
                        Some(b'0'..=b'9') => current_index += 1,
                        // All other legal characters
                        Some(10 | 32..=126) => break,
                        Some(c) => bail!("illegal character {c:?} while lexing a number"),
                        None => bail!("Unexpected end of file while lexing a number"),
                    }
                }

                let s = &str_input[index..current_index];

                string_map.push(s);
                let next_index = string_map.len() - 1;

                if is_float {
                    tokens.push(Token::new(TokenType::FLOATVAL).set_index(next_index));
                } else {
                    tokens.push(Token::new(TokenType::INTVAL).set_index(next_index));
                }

                index = current_index;
            }
            Some(b'.') => {
                if let Some(b'0'..=b'9') = input.get(index + 1) {
                    let mut current_index = index + 2;
                    loop {
                        match input.get(current_index) {
                            Some(b'.') => break,
                            Some(b'0'..=b'9') => current_index += 1,
                            // All other legal characters
                            #[allow(clippy::match_same_arms)]
                            Some(10 | 32..=126) => break,
                            Some(c) => bail!("illegal character {c:?} while lexing a number"),
                            None => bail!("Unexpected end of file while lexing a number"),
                        }
                    }

                    let s = &str_input[index..current_index];

                    string_map.push(s);
                    let next_index = string_map.len() - 1;

                    tokens.push(Token::new(TokenType::FLOATVAL).set_index(next_index));

                    index = current_index;
                } else {
                    tokens.push(TokenType::DOT.into());
                    index += 1;
                }
            }
            Some(b'"') => {
                let mut current_index = index + 1;
                loop {
                    match input.get(current_index) {
                        Some(b'"') => break,
                        Some(b'\n') => bail!("newline found in string literal"),
                        Some(32..=126) => current_index += 1,
                        Some(c) => bail!("illegal character {c:?} while lexing a string"),
                        None => bail!("Unexpected end of file while lexing a string"),
                    }
                }

                let s = &str_input[index + 1..current_index];

                string_map.push(s);
                let next_index = string_map.len() - 1;

                tokens.push(Token::new(TokenType::STRING).set_index(next_index));
                index = current_index + 1; // skip the closing "
            }
            Some(b'a'..=b'z' | b'A'..=b'Z') => {
                let mut current_index = index + 1;
                loop {
                    match input.get(current_index) {
                        Some(b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_') => {
                            current_index += 1;
                        }
                        None | Some(10 | 32..=126) => break,
                        Some(c) => bail!("illegal character {c:?} while lexing a variable"),
                    }
                }

                let s = &str_input[index..current_index];

                let token = match s {
                    "array" => TokenType::ARRAY.into(),
                    "assert" => TokenType::ASSERT.into(),
                    "bool" => TokenType::BOOL.into(),
                    "else" => TokenType::ELSE.into(),
                    "false" => TokenType::FALSE.into(),
                    "float" => TokenType::FLOAT.into(),
                    "fn" => TokenType::FN.into(),
                    "if" => TokenType::IF.into(),
                    "image" => TokenType::IMAGE.into(),
                    "int" => TokenType::INT.into(),
                    "let" => TokenType::LET.into(),
                    "print" => TokenType::PRINT.into(),
                    "read" => TokenType::READ.into(),
                    "return" => TokenType::RETURN.into(),
                    "show" => TokenType::SHOW.into(),
                    "struct" => TokenType::STRUCT.into(),
                    "sum" => TokenType::SUM.into(),
                    "then" => TokenType::THEN.into(),
                    "time" => TokenType::TIME.into(),
                    "to" => TokenType::TO.into(),
                    "true" => TokenType::TRUE.into(),
                    "void" => TokenType::VOID.into(),
                    "write" => TokenType::WRITE.into(),
                    "type" => TokenType::TYPE.into(),
                    s => {
                        string_map.push(s);
                        let next_index = string_map.len() - 1;
                        Token::new(TokenType::VARIABLE).set_index(next_index)
                    }
                };

                tokens.push(token);
                index = current_index;
            }
            Some(b'\n') => {
                if tokens.last().map(Token::get_type) != Some(TokenType::NEWLINE) {
                    tokens.push(TokenType::NEWLINE.into());
                }
                index += 1;
            }

            Some(b'&') => {
                if let Some(b'&') = input.get(index + 1) {
                    tokens.push(TokenType::And.into());
                    index += 2;
                } else {
                    bail!("Unexpected single '&' found while lexing");
                }
            }
            Some(b'|') => {
                if let Some(b'|') = input.get(index + 1) {
                    tokens.push(TokenType::Or.into());
                    index += 2;
                } else {
                    bail!("Unexpected single '|' found while lexing");
                }
            }
            Some(b'=') => {
                if let Some(b'=') = input.get(index + 1) {
                    tokens.push(TokenType::Eq.into());
                    index += 2;
                } else {
                    tokens.push(TokenType::EQUALS.into());
                    index += 1;
                }
            }
            Some(b'>') => {
                if let Some(b'=') = input.get(index + 1) {
                    tokens.push(TokenType::GreaterEq.into());
                    index += 2;
                } else {
                    tokens.push(TokenType::Greater.into());
                    index += 1;
                }
            }
            Some(b'<') => {
                if let Some(b'=') = input.get(index + 1) {
                    tokens.push(TokenType::LessEq.into());
                    index += 2;
                } else {
                    tokens.push(TokenType::Less.into());
                    index += 1;
                }
            }
            Some(b'+') => {
                tokens.push(TokenType::Add.into());
                index += 1;
            }
            Some(b'-') => {
                tokens.push(TokenType::Sub.into());
                index += 1;
            }
            Some(b'*') => {
                tokens.push(TokenType::Mul.into());
                index += 1;
            }
            Some(b'%') => {
                tokens.push(TokenType::Mod.into());
                index += 1;
            }
            Some(b'!') => {
                if let Some(b'=') = input.get(index + 1) {
                    tokens.push(TokenType::Neq.into());
                    index += 2;
                } else {
                    tokens.push(TokenType::Not.into());
                    index += 1;
                }
            }
            Some(b'{') => {
                tokens.push(TokenType::LCURLY.into());
                index += 1;
            }
            Some(b'}') => {
                tokens.push(TokenType::RCURLY.into());
                index += 1;
            }
            Some(b'(') => {
                tokens.push(TokenType::LPAREN.into());
                index += 1;
            }
            Some(b')') => {
                tokens.push(TokenType::RPAREN.into());
                index += 1;
            }
            Some(b'[') => {
                tokens.push(TokenType::LSQUARE.into());
                index += 1;
            }
            Some(b']') => {
                tokens.push(TokenType::RSQUARE.into());
                index += 1;
            }
            Some(b':') => {
                tokens.push(TokenType::COLON.into());
                index += 1;
            }
            Some(b',') => {
                tokens.push(TokenType::COMMA.into());
                index += 1;
            }
            Some(c) => bail!("illegal character '{}' found while lexing", *c as char),
        }

        #[cfg(test)]
        if index == last_loop_index {
            println!("Remainder: {:?}", &str_input[index..]);
            debug_assert!(false, "Loop did not advance");
        }
    }

    Ok((tokens, string_map))
}

#[allow(clippy::too_many_lines)]
#[allow(clippy::range_plus_one)]
#[allow(clippy::must_use_candidate)]
pub fn input_by_token(str_input: &str, capacity: usize) -> Vec<&str> {
    measure!("input_by_token");
    let mut input_by_token = Vec::with_capacity(capacity);
    let mut skip_newlines_at = 0;

    let input = str_input.as_bytes();
    let mut index = 0;

    loop {
        match input.get(index) {
            None => break,
            Some(b' ') => index += 1,
            Some(b'\\') => index += 2,
            Some(b'/') => match input.get(index + 1) {
                Some(b'*') => {
                    let mut current_index = index + 2;
                    loop {
                        match input.get(current_index) {
                            Some(b'*') => {
                                if let Some(b'/') = input.get(current_index + 1) {
                                    break;
                                }

                                current_index += 1;
                            }
                            _ => current_index += 1,
                        }
                    }
                    index = current_index + 2;
                }
                Some(b'/') => {
                    let mut current_index = index + 2;
                    loop {
                        match input.get(current_index) {
                            Some(b'\n') => break,
                            _ => current_index += 1,
                        }
                    }
                    // include the newline
                    current_index += 1;

                    if skip_newlines_at == input_by_token.len() {
                        input_by_token.push(&str_input[index..current_index]);
                        skip_newlines_at = input_by_token.len();
                    }

                    index = current_index;
                }
                _ => {
                    input_by_token.push(&str_input[index..index + 1]);
                    index += 1;
                }
            },
            Some(b'0'..=b'9') => {
                let mut current_index = index + 1;
                let mut is_float = false;
                loop {
                    match input.get(current_index) {
                        Some(b'.') => {
                            if is_float {
                                break;
                            }
                            is_float = true;
                            current_index += 1;
                        }
                        Some(b'0'..=b'9') => current_index += 1,
                        // All other legal characters
                        _ => break,
                    }
                }

                let s = &str_input[index..current_index];
                input_by_token.push(s);
                index = current_index;
            }
            Some(b'.') => {
                if let Some(b'0'..=b'9') = input.get(index + 1) {
                    let mut current_index = index + 2;
                    while let Some(b'0'..=b'9') = input.get(current_index) {
                        current_index += 1;
                    }

                    let s = &str_input[index..current_index];

                    input_by_token.push(s);

                    index = current_index;
                } else {
                    input_by_token.push(&str_input[index..index + 1]);
                    index += 1;
                }
            }
            Some(b'"') => {
                let mut current_index = index + 1;
                loop {
                    match input.get(current_index) {
                        Some(b'"') => break,
                        _ => current_index += 1,
                    }
                }

                input_by_token.push(&str_input[index..current_index + 1]); // Keep the " in the capture
                index = current_index + 1; // skip the closing "
            }
            Some(b'a'..=b'z' | b'A'..=b'Z') => {
                let mut current_index = index + 1;
                while let Some(b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_') =
                    input.get(current_index)
                {
                    current_index += 1;
                }
                input_by_token.push(&str_input[index..current_index]);
                index = current_index;
            }
            Some(b'\n') => {
                if skip_newlines_at != input_by_token.len() {
                    input_by_token.push(&str_input[index..index + 1]);
                    skip_newlines_at = input_by_token.len();
                }
                index += 1;
            }
            Some(b'=' | b'>' | b'<' | b'!') => {
                if let Some(b'=') = input.get(index + 1) {
                    input_by_token.push(&str_input[index..index + 2]);
                    index += 2;
                } else {
                    input_by_token.push(&str_input[index..index + 1]);
                    index += 1;
                }
            }
            Some(b'&' | b'|') => {
                input_by_token.push(&str_input[index..index + 2]);
                index += 2;
            }
            Some(
                b'+' | b'-' | b'*' | b'%' | b'{' | b'}' | b'(' | b')' | b'[' | b']' | b':' | b',',
            ) => {
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            _ => unreachable!(),
        }
    }

    input_by_token
}

#[test]
fn test_lex_correct() {
    test_correct(
        "grader/hw2/lexer-tests1",
        |file: &str, solution_file: &str| {
            let (tokens, string_map) = lex(file).unwrap();

            let mut output = String::new();

            for token in tokens {
                token.fmt(&mut output, &string_map).unwrap();
                output.push('\n');
            }

            pretty_assertions::assert_eq!(output, solution_file);
        },
    );
}

#[test]
fn test_lex_success() {
    test_solos("grader/hw2/lexer-tests2", |file, _| {
        assert!(lex(file).is_ok());
    });
}

#[test]
fn test_lex_fails() {
    test_solos("grader/hw2/lexer-tests3", |file, _| {
        assert!(lex(file).is_err());
    });
}
