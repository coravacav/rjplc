use color_eyre::eyre::{bail, Result};
use nom::{
    branch::alt,
    bytes::complete::{tag, take_till, take_until, take_while},
    character::complete::{char, digit1, satisfy},
    combinator::{fail, map, opt, recognize, value},
    multi::many1,
    sequence::{delimited, preceded, terminated, tuple},
    Finish,
};

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
    Eq,
    Greater,
    Less,
    And,
    GreaterEq,
    LessEq,
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Op::Add => write!(f, "+"),
            Op::Sub => write!(f, "-"),
            Op::Mul => write!(f, "*"),
            Op::Div => write!(f, "/"),
            Op::Mod => write!(f, "%"),
            Op::Not => write!(f, "!"),
            Op::Eq => write!(f, "=="),
            Op::Greater => write!(f, ">"),
            Op::Less => write!(f, "<"),
            Op::And => write!(f, "&&"),
            Op::GreaterEq => write!(f, ">="),
            Op::LessEq => write!(f, "<="),
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[allow(non_camel_case_types, clippy::upper_case_acronyms)]
pub enum Token<'a> {
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
    FLOATVAL(&'a str),
    FN,
    IF,
    IMAGE,
    INT,
    INTVAL(&'a str),
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
    STRING(&'a str),
    STRUCT,
    SUM,
    THEN,
    TIME,
    TO,
    TRUE,
    VARIABLE(&'a str),
    VOID,
    WRITE,
    TYPE,
}

impl PartialEq for Token<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Token::FLOATVAL(a), Token::FLOATVAL(b)) => a.as_ptr() == b.as_ptr(),
            (Token::INTVAL(a), Token::INTVAL(b)) => a.as_ptr() == b.as_ptr(),
            (Token::STRING(a), Token::STRING(b)) => a.as_ptr() == b.as_ptr(),
            (Token::VARIABLE(a), Token::VARIABLE(b)) => a.as_ptr() == b.as_ptr(),
            _ => std::mem::discriminant(self) == std::mem::discriminant(other),
        }
    }
}

impl std::fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::ARRAY => write!(f, "ARRAY 'array'"),
            Token::ASSERT => write!(f, "ASSERT 'assert'"),
            Token::BOOL => write!(f, "BOOL 'bool'"),
            Token::COLON => write!(f, "COLON ':'"),
            Token::COMMA => write!(f, "COMMA ','"),
            Token::DOT => write!(f, "DOT '.'"),
            Token::ELSE => write!(f, "ELSE 'else'"),
            Token::END_OF_FILE => write!(f, "END_OF_FILE"),
            Token::EQUALS => write!(f, "EQUALS '='"),
            Token::FALSE => write!(f, "FALSE 'false'"),
            Token::FLOAT => write!(f, "FLOAT 'float'"),
            Token::FLOATVAL(s) => write!(f, "FLOATVAL '{s}'"),
            Token::FN => write!(f, "FN 'fn'"),
            Token::IF => write!(f, "IF 'if'"),
            Token::IMAGE => write!(f, "IMAGE 'image'"),
            Token::INT => write!(f, "INT 'int'"),
            Token::INTVAL(s) => write!(f, "INTVAL '{s}'"),
            Token::LCURLY => write!(f, "LCURLY '{{'"),
            Token::LET => write!(f, "LET 'let'"),
            Token::LPAREN => write!(f, "LPAREN '('"),
            Token::LSQUARE => write!(f, "LSQUARE '['"),
            Token::NEWLINE => write!(f, "NEWLINE"),
            Token::OP(op) => write!(f, "OP '{op}'"),
            Token::PRINT => write!(f, "PRINT 'print'"),
            Token::RCURLY => write!(f, "RCURLY '}}'"),
            Token::READ => write!(f, "READ 'read'"),
            Token::RETURN => write!(f, "RETURN 'return'"),
            Token::RPAREN => write!(f, "RPAREN ')'"),
            Token::RSQUARE => write!(f, "RSQUARE ']'"),
            Token::SHOW => write!(f, "SHOW 'show'"),
            Token::STRING(s) => write!(f, "STRING '\"{s}\"'"),
            Token::STRUCT => write!(f, "STRUCT 'struct'"),
            Token::SUM => write!(f, "SUM 'sum'"),
            Token::THEN => write!(f, "THEN 'then'"),
            Token::TIME => write!(f, "TIME 'time'"),
            Token::TO => write!(f, "TO 'to'"),
            Token::TRUE => write!(f, "TRUE 'true'"),
            Token::VARIABLE(s) => write!(f, "VARIABLE '{s}'"),
            Token::VOID => write!(f, "VOID 'void'"),
            Token::WRITE => write!(f, "WRITE 'write'"),
            Token::TYPE => write!(f, "TYPE 'type'"),
        }
    }
}

pub trait LexImplementation {
    fn lex(input: &str) -> Result<(Vec<Token>, Vec<&str>)>;
}

pub struct LexNom;

impl LexNom {
    fn int(input: &str) -> nom::IResult<&str, Token> {
        map(digit1, Token::INTVAL)(input)
    }

    fn float(input: &str) -> nom::IResult<&str, Token> {
        map(
            alt((
                recognize(delimited(digit1, char('.'), opt(digit1))),
                recognize(preceded(char('.'), digit1)),
            )),
            Token::FLOATVAL,
        )(input)
    }

    fn num(input: &str) -> nom::IResult<&str, Token> {
        alt((Self::float, Self::int))(input)
    }

    fn string(input: &str) -> nom::IResult<&str, Token> {
        map(
            delimited(char('"'), take_till(|c| matches!(c, '"' | '\n')), char('"')),
            Token::STRING,
        )(input)
    }

    fn variable_or_keyword(input: &str) -> nom::IResult<&str, Token> {
        map(
            recognize(tuple((
                satisfy(|c| c.is_ascii_alphabetic()),
                take_while(|c: char| c.is_ascii_alphanumeric() || c == '_'),
            ))),
            |s: &str| match s {
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
                s => Token::VARIABLE(s),
            },
        )(input)
    }

    fn op_and_symbol(input: &str) -> nom::IResult<&str, Token> {
        match input.get(0..2) {
            Some("&&") => return Ok((&input[2..], Token::OP(Op::And))),
            Some("==") => return Ok((&input[2..], Token::OP(Op::Eq))),
            Some(">=") => return Ok((&input[2..], Token::OP(Op::GreaterEq))),
            Some("<=") => return Ok((&input[2..], Token::OP(Op::LessEq))),
            _ => {}
        };

        match input.get(0..1) {
            Some("+") => Ok((&input[1..], Token::OP(Op::Add))),
            Some("-") => Ok((&input[1..], Token::OP(Op::Sub))),
            Some("*") => Ok((&input[1..], Token::OP(Op::Mul))),
            Some("/") => Ok((&input[1..], Token::OP(Op::Div))),
            Some("%") => Ok((&input[1..], Token::OP(Op::Mod))),
            Some("!") => Ok((&input[1..], Token::OP(Op::Not))),
            Some(">") => Ok((&input[1..], Token::OP(Op::Greater))),
            Some("<") => Ok((&input[1..], Token::OP(Op::Less))),
            Some("=") => Ok((&input[1..], Token::EQUALS)),
            Some("{") => Ok((&input[1..], Token::LCURLY)),
            Some("}") => Ok((&input[1..], Token::RCURLY)),
            Some("(") => Ok((&input[1..], Token::LPAREN)),
            Some(")") => Ok((&input[1..], Token::RPAREN)),
            Some("[") => Ok((&input[1..], Token::LSQUARE)),
            Some("]") => Ok((&input[1..], Token::RSQUARE)),
            Some(":") => Ok((&input[1..], Token::COLON)),
            Some(",") => Ok((&input[1..], Token::COMMA)),
            Some(".") => Ok((&input[1..], Token::DOT)),
            _ => fail(input),
        }
    }

    pub fn nom_lex(input: &str) -> nom::IResult<&str, (Vec<Token>, Vec<&str>)> {
        let mut acc = vec![];
        let mut input_by_token = vec![];

        let mut input = input;

        loop {
            if input.is_empty() {
                break;
            }

            let (remaining_input, token) = alt((
                map(many1(Self::spaces_and_comments), |_| None),
                map(
                    alt((
                        Self::num,
                        Self::string,
                        Self::variable_or_keyword,
                        value(
                            Token::NEWLINE,
                            terminated(opt(preceded(tag("//"), take_until("\n"))), char('\n')),
                        ),
                        Self::op_and_symbol,
                    )),
                    Option::Some,
                ),
            ))(input)?;

            let consumed_input = &input[..input.len() - remaining_input.len()];

            input = remaining_input;

            match token {
                Some(Token::NEWLINE) if acc.last() == Some(&Token::NEWLINE) => {}
                Some(token) => {
                    acc.push(token);
                    input_by_token.push(consumed_input);
                }
                None => {}
            }
        }

        Ok((input, (acc, (input_by_token))))
    }

    fn spaces_and_comments(input: &str) -> nom::IResult<&str, &str> {
        alt((
            recognize(many1(char(' '))),
            recognize(delimited(tag("/*"), take_until("*/"), tag("*/"))),
            recognize(tag("\\\n")),
        ))(input)
    }
}

pub struct LexLinear;

impl LexImplementation for LexNom {
    fn lex(input: &str) -> Result<(Vec<Token>, Vec<&str>)> {
        if let Some(c) = input.chars().find(|&c| !matches!(c as u32, 10 | 32..=126)) {
            bail!("invalid character {c:?}");
        }

        let (input, (mut tokens, input_by_token)) = LexNom::nom_lex(input)
            .finish()
            .map_err(|e| color_eyre::eyre::eyre!("{e}"))?;

        debug_assert_eq!(tokens.len(), input_by_token.len());

        if input.is_empty() {
            tokens.push(Token::END_OF_FILE);
        } else {
            bail!("could not lex entire input");
        }

        Ok((tokens, input_by_token))
    }
}

impl LexImplementation for LexLinear {
    fn lex(str_input: &str) -> Result<(Vec<Token>, Vec<&str>)> {
        let mut acc = vec![];
        let mut input_by_token = vec![];

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
                                    bail!("Illegal character {c:?} while parsing a block comment")
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
                                    bail!("Illegal character {c:?} while parsing a line comment")
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
                            Some(c) => bail!("Illegal character {c:?} while parsing a number"),
                            None => bail!("Unexpected end of file while parsing a number"),
                        }
                    }

                    let s = &str_input[index..current_index];

                    if is_float {
                        acc.push(Token::FLOATVAL(s));
                    } else {
                        acc.push(Token::INTVAL(s));
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
                                Some(10 | 32..=126) => break,
                                Some(c) => bail!("Illegal character {c:?} while parsing a number"),
                                None => bail!("Unexpected end of file while parsing a number"),
                            }
                        }

                        let s = &str_input[index..current_index];

                        acc.push(Token::FLOATVAL(s));
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
                            Some(c) => bail!("Illegal character {c:?} while parsing a string"),
                            None => bail!("Unexpected end of file while parsing a string"),
                        }
                    }

                    acc.push(Token::STRING(&str_input[index + 1..current_index]));
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
                            Some(c) => bail!("Illegal character {c:?} while parsing a variable"),
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
                        s => Token::VARIABLE(s),
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
                        bail!("Unexpected single '&' found while parsing");
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
                    acc.push(Token::OP(Op::Not));
                    input_by_token.push(&str_input[index..index + 1]);
                    index += 1;
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
                Some(c) => bail!("Illegal character '{}' found while parsing", *c as char),
            }

            #[cfg(test)]
            if index == last_loop_index {
                println!("Remainder: {:?}", &str_input[index..]);
                panic!("Loop did not advance");
            }
        }

        Ok((acc, input_by_token))
    }
}

#[test]
fn test_lex_correct() {
    test_correct(
        "grader/hw2/lexer-tests1",
        |file: &str, solution_file: &str| {
            let (tokens, captures) = LexNom::lex(file).unwrap();
            let (tokens_linear, captures_linear) = LexLinear::lex(file).unwrap();

            pretty_assertions::assert_eq!(tokens, tokens_linear);
            pretty_assertions::assert_eq!(captures, captures_linear);

            let mut output = String::new();

            for token in tokens {
                use std::fmt::Write;
                writeln!(output, "{}", token).unwrap();
            }

            pretty_assertions::assert_eq!(output, solution_file);
        },
    );
}

#[test]
fn test_lex_success() {
    test_solos("grader/hw2/lexer-tests2", |file, _| {
        let (tokens, captures) = LexNom::lex(file).unwrap();
        let (tokens_linear, captures_linear) = LexLinear::lex(file).unwrap();

        pretty_assertions::assert_eq!(tokens, tokens_linear);
        pretty_assertions::assert_eq!(captures, captures_linear);
    });
}

#[test]
fn test_lex_fails() {
    test_solos("grader/hw2/lexer-tests3", |file, _| {
        assert!(LexNom::lex(file).is_err());
        assert!(LexLinear::lex(file).is_err());
    });
}
