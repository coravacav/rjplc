use color_eyre::eyre::Result;
use nom::{
    branch::alt,
    bytes::complete::{tag, take_till, take_until, take_while},
    character::complete::{char, digit1, one_of, satisfy},
    combinator::{map, opt, recognize, value},
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
    alt((float, int))(input)
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

fn op(input: &str) -> nom::IResult<&str, Token> {
    map(
        alt((
            tag("=="),
            tag("&&"),
            tag(">="),
            tag("<="),
            recognize(one_of("+-*/%!><")),
        )),
        |s: &str| {
            Token::OP(match s {
                "==" => Op::Eq,
                "+" => Op::Add,
                "-" => Op::Sub,
                "*" => Op::Mul,
                "/" => Op::Div,
                "%" => Op::Mod,
                "!" => Op::Not,
                ">" => Op::Greater,
                "<" => Op::Less,
                "&&" => Op::And,
                ">=" => Op::GreaterEq,
                "<=" => Op::LessEq,
                _ => unreachable!("Invalid op"),
            })
        },
    )(input)
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
            map(many1(spaces_and_comments), |_| None),
            map(
                alt((
                    num,
                    string,
                    variable_or_keyword,
                    value(
                        Token::NEWLINE,
                        terminated(opt(preceded(tag("//"), take_until("\n"))), char('\n')),
                    ),
                    op,
                    value(Token::EQUALS, tag("=")),
                    value(Token::LCURLY, tag("{")),
                    value(Token::RCURLY, tag("}")),
                    value(Token::LPAREN, tag("(")),
                    value(Token::RPAREN, tag(")")),
                    value(Token::LSQUARE, tag("[")),
                    value(Token::RSQUARE, tag("]")),
                    value(Token::COLON, tag(":")),
                    value(Token::COMMA, tag(",")),
                    value(Token::DOT, tag(".")),
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

pub fn lex(input: &str) -> Result<(Vec<Token>, Vec<&str>)> {
    if let Some(c) = input.chars().find(|&c| !matches!(c as u32, 10 | 32..=126)) {
        color_eyre::eyre::bail!("invalid character {c:?}");
    }

    let (input, (mut tokens, input_by_token)) = nom_lex(input)
        .finish()
        .map_err(|e| color_eyre::eyre::eyre!("{e}"))?;

    debug_assert_eq!(tokens.len(), input_by_token.len());

    if input.is_empty() {
        tokens.push(Token::END_OF_FILE);
    } else {
        // #[cfg(test)]
        // dbg!(input);
        color_eyre::eyre::bail!("could not lex entire input");
    }

    Ok((tokens, input_by_token))
}

#[test]
fn test_lex_correct() {
    test_correct(
        "grader/hw2/lexer-tests1",
        |file: &str, solution_file: &str| {
            let (tokens, _) = lex(file).unwrap();

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
    test_solos("grader/hw2/lexer-tests2", |file| {
        let file = file.unwrap();
        assert!(lex(file).is_ok());
    });
}

#[test]
fn test_lex_fails() {
    test_solos("grader/hw2/lexer-tests3", |file| {
        let Some(file) = file else {
            return;
        };

        assert!(lex(file).is_err());
    });
}
