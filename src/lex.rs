use std::fmt::Write;

use color_eyre::eyre::{bail, Result};

use crate::{measure, CustomDisplay};
#[cfg(test)]
use crate::{test_correct, test_solos};

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum Op {
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
}

impl CustomDisplay for Op {
    fn fmt(&self, f: &mut String, _string_map: &[&str]) -> std::fmt::Result {
        match self {
            Op::Add => f.write_char('+'),
            Op::Sub => f.write_char('-'),
            Op::Mul => f.write_char('*'),
            Op::Div => f.write_char('/'),
            Op::Mod => f.write_char('%'),
            Op::Not => f.write_char('!'),
            Op::Greater => f.write_char('>'),
            Op::Less => f.write_char('<'),
            Op::Eq => f.write_str("=="),
            Op::Neq => f.write_str("!="),
            Op::And => f.write_str("&&"),
            Op::Or => f.write_str("||"),
            Op::GreaterEq => f.write_str(">="),
            Op::LessEq => f.write_str("<="),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[allow(non_camel_case_types, clippy::upper_case_acronyms)]
pub enum Token {
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
    FLOATVAL(usize),
    FN,
    IF,
    IMAGE,
    INT,
    INTVAL(usize),
    LCURLY,
    LET,
    LPAREN,
    LSQUARE,
    NEWLINE,
    OP(Op),
    PRINT,
    RCURLY,
    READ,
    RETURN,
    RPAREN,
    RSQUARE,
    SHOW,
    STRING(usize),
    STRUCT,
    SUM,
    THEN,
    TIME,
    TO,
    TRUE,
    VARIABLE(usize),
    VOID,
    WRITE,
    TYPE,
}

impl CustomDisplay for Token {
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result {
        match self {
            Token::ARRAY => f.write_str("ARRAY 'array'"),
            Token::ASSERT => f.write_str("ASSERT 'assert'"),
            Token::BOOL => f.write_str("BOOL 'bool'"),
            Token::COLON => f.write_str("COLON ':'"),
            Token::COMMA => f.write_str("COMMA ','"),
            Token::DOT => f.write_str("DOT '.'"),
            Token::ELSE => f.write_str("ELSE 'else'"),
            Token::END_OF_FILE => f.write_str("END_OF_FILE"),
            Token::EQUALS => f.write_str("EQUALS '='"),
            Token::FALSE => f.write_str("FALSE 'false'"),
            Token::FLOAT => f.write_str("FLOAT 'float'"),
            Token::FN => f.write_str("FN 'fn'"),
            Token::IF => f.write_str("IF 'if'"),
            Token::IMAGE => f.write_str("IMAGE 'image'"),
            Token::INT => f.write_str("INT 'int'"),
            Token::LCURLY => f.write_str("LCURLY '{'"),
            Token::LET => f.write_str("LET 'let'"),
            Token::LPAREN => f.write_str("LPAREN '('"),
            Token::LSQUARE => f.write_str("LSQUARE '['"),
            Token::NEWLINE => f.write_str("NEWLINE"),
            Token::OP(op) => {
                f.write_str("OP '")?;
                op.fmt(f, string_map)?;
                f.write_char('\'')
            }
            Token::PRINT => f.write_str("PRINT 'print'"),
            Token::RCURLY => f.write_str("RCURLY '}'"),
            Token::READ => f.write_str("READ 'read'"),
            Token::RETURN => f.write_str("RETURN 'return'"),
            Token::RPAREN => f.write_str("RPAREN ')'"),
            Token::RSQUARE => f.write_str("RSQUARE ']'"),
            Token::SHOW => f.write_str("SHOW 'show'"),
            Token::STRUCT => f.write_str("STRUCT 'struct'"),
            Token::SUM => f.write_str("SUM 'sum'"),
            Token::THEN => f.write_str("THEN 'then'"),
            Token::TIME => f.write_str("TIME 'time'"),
            Token::TO => f.write_str("TO 'to'"),
            Token::TRUE => f.write_str("TRUE 'true'"),
            Token::VOID => f.write_str("VOID 'void'"),
            Token::WRITE => f.write_str("WRITE 'write'"),
            Token::TYPE => f.write_str("TYPE 'type'"),
            Token::VARIABLE(s) => {
                f.write_str("VARIABLE '")?;
                f.write_str(string_map[*s])?;
                f.write_char('\'')
            }
            Token::STRING(s) => {
                f.write_str("STRING '\"")?;
                f.write_str(string_map[*s])?;
                f.write_str("\"'")
            }
            Token::FLOATVAL(s) => {
                f.write_str("FLOATVAL '")?;
                f.write_str(string_map[*s])?;
                f.write_char('\'')
            }
            Token::INTVAL(s) => {
                f.write_str("INTVAL '")?;
                f.write_str(string_map[*s])?;
                f.write_char('\'')
            }
        }
    }
}

/// # Errors
/// Failed to lex.
#[allow(clippy::too_many_lines)]
#[allow(clippy::range_plus_one)]
pub fn lex(str_input: &str) -> Result<(Vec<Token>, Vec<&str>, Vec<&str>)> {
    measure!("lex");
    let mut acc = vec![];
    let mut input_by_token = vec![];
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
            None => break acc.push(Token::END_OF_FILE),
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

                    if acc.last() != Some(&Token::NEWLINE) {
                        acc.push(Token::NEWLINE);
                        input_by_token.push(&str_input[index..current_index]);
                    }

                    index = current_index;
                }
                _ => {
                    acc.push(Token::OP(Op::Div));
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
                        Some(10 | 32..=126) => break,
                        Some(c) => bail!("illegal character {c:?} while lexing a number"),
                        None => bail!("Unexpected end of file while lexing a number"),
                    }
                }

                let s = &str_input[index..current_index];

                string_map.push(s);
                let next_index = string_map.len() - 1;

                if is_float {
                    acc.push(Token::FLOATVAL(next_index));
                } else {
                    acc.push(Token::INTVAL(next_index));
                }

                input_by_token.push(s);

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

                    acc.push(Token::FLOATVAL(next_index));
                    input_by_token.push(s);

                    index = current_index;
                } else {
                    acc.push(Token::DOT);
                    input_by_token.push(&str_input[index..index + 1]);
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

                string_map.push(&str_input[index + 1..current_index]);
                let next_index = string_map.len() - 1;

                acc.push(Token::STRING(next_index));
                input_by_token.push(&str_input[index..current_index + 1]); // Keep the " in the capture
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
                    "array" => Token::ARRAY,
                    "assert" => Token::ASSERT,
                    "bool" => Token::BOOL,
                    "else" => Token::ELSE,
                    "false" => Token::FALSE,
                    "float" => Token::FLOAT,
                    "fn" => Token::FN,
                    "if" => Token::IF,
                    "image" => Token::IMAGE,
                    "int" => Token::INT,
                    "let" => Token::LET,
                    "print" => Token::PRINT,
                    "read" => Token::READ,
                    "return" => Token::RETURN,
                    "show" => Token::SHOW,
                    "struct" => Token::STRUCT,
                    "sum" => Token::SUM,
                    "then" => Token::THEN,
                    "time" => Token::TIME,
                    "to" => Token::TO,
                    "true" => Token::TRUE,
                    "void" => Token::VOID,
                    "write" => Token::WRITE,
                    "type" => Token::TYPE,
                    s => {
                        string_map.push(s);
                        let next_index = string_map.len() - 1;
                        Token::VARIABLE(next_index)
                    }
                };

                acc.push(token);
                input_by_token.push(s);
                index = current_index;
            }
            Some(b'\n') => {
                if acc.last() != Some(&Token::NEWLINE) {
                    acc.push(Token::NEWLINE);
                    input_by_token.push(&str_input[index..index + 1]);
                }
                index += 1;
            }

            Some(b'&') => {
                if let Some(b'&') = input.get(index + 1) {
                    acc.push(Token::OP(Op::And));
                    input_by_token.push(&str_input[index..index + 2]);
                    index += 2;
                } else {
                    bail!("Unexpected single '&' found while lexing");
                }
            }
            Some(b'|') => {
                if let Some(b'|') = input.get(index + 1) {
                    acc.push(Token::OP(Op::Or));
                    input_by_token.push(&str_input[index..index + 2]);
                    index += 2;
                } else {
                    bail!("Unexpected single '|' found while lexing");
                }
            }
            Some(b'=') => {
                if let Some(b'=') = input.get(index + 1) {
                    acc.push(Token::OP(Op::Eq));
                    input_by_token.push(&str_input[index..index + 2]);
                    index += 2;
                } else {
                    acc.push(Token::EQUALS);
                    input_by_token.push(&str_input[index..index + 1]);
                    index += 1;
                }
            }
            Some(b'>') => {
                if let Some(b'=') = input.get(index + 1) {
                    acc.push(Token::OP(Op::GreaterEq));
                    input_by_token.push(&str_input[index..index + 2]);
                    index += 2;
                } else {
                    acc.push(Token::OP(Op::Greater));
                    input_by_token.push(&str_input[index..index + 1]);
                    index += 1;
                }
            }
            Some(b'<') => {
                if let Some(b'=') = input.get(index + 1) {
                    acc.push(Token::OP(Op::LessEq));
                    input_by_token.push(&str_input[index..index + 2]);
                    index += 2;
                } else {
                    acc.push(Token::OP(Op::Less));
                    input_by_token.push(&str_input[index..index + 1]);
                    index += 1;
                }
            }
            Some(b'+') => {
                acc.push(Token::OP(Op::Add));
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            Some(b'-') => {
                acc.push(Token::OP(Op::Sub));
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            Some(b'*') => {
                acc.push(Token::OP(Op::Mul));
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            Some(b'%') => {
                acc.push(Token::OP(Op::Mod));
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            Some(b'!') => {
                if let Some(b'=') = input.get(index + 1) {
                    acc.push(Token::OP(Op::Neq));
                    input_by_token.push(&str_input[index..index + 2]);
                    index += 2;
                } else {
                    acc.push(Token::OP(Op::Not));
                    input_by_token.push(&str_input[index..index + 1]);
                    index += 1;
                }
            }
            Some(b'{') => {
                acc.push(Token::LCURLY);
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            Some(b'}') => {
                acc.push(Token::RCURLY);
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            Some(b'(') => {
                acc.push(Token::LPAREN);
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            Some(b')') => {
                acc.push(Token::RPAREN);
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            Some(b'[') => {
                acc.push(Token::LSQUARE);
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            Some(b']') => {
                acc.push(Token::RSQUARE);
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            Some(b':') => {
                acc.push(Token::COLON);
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            Some(b',') => {
                acc.push(Token::COMMA);
                input_by_token.push(&str_input[index..index + 1]);
                index += 1;
            }
            // All other legal characters
            // Some(32..=126) => {}
            Some(c) => bail!("illegal character '{}' found while lexing", *c as char),
        }

        #[cfg(test)]
        if index == last_loop_index {
            println!("Remainder: {:?}", &str_input[index..]);
            debug_assert!(false, "Loop did not advance");
        }
    }

    Ok((acc, input_by_token, string_map))
}

#[test]
fn test_lex_correct() {
    test_correct(
        "grader/hw2/lexer-tests1",
        |file: &str, solution_file: &str| {
            let (tokens, _, string_map) = lex(file).unwrap();

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
