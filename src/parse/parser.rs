use colored::Colorize;
use itertools::Itertools;

use crate::{
    lex::{input_by_token, Token, TokenType},
    undo_slice_by_cuts, UndoSliceSelection,
};

pub(crate) trait Consume<'a, 'b>: Sized {
    fn consume(parser: Parser, data: &'b StaticParserData<'a>) -> ParseResult<'a, Self>;
}

pub(crate) enum ParseResult<'a, T> {
    NotParsedErrorPrinted {
        error_message: Box<dyn Fn() -> String + 'a>,
        line: usize,
        column: usize,
    },
    NotParsed {
        error_message: Box<dyn Fn() -> String + 'a>,
        position: usize,
    },
    Parsed(Parser, T),
}

macro_rules! miss {
    ($parser:ident, $($msg:tt)*) => {
        return $parser.miss(Box::new(move || format!($($msg)*)))
    };
}

macro_rules! consume {
    ($parser:ident, $data:ident, $type:ty, $outvar:ident) => {
        let (advanced_parser, $outvar) = match <$type>::consume($parser, $data) {
            ParseResult::Parsed(parser, t) => {
                debug_assert_ne!($parser.current_position, parser.current_position);
                (parser, t)
            }
            ParseResult::NotParsed {
                error_message,
                position,
            } => {
                return ParseResult::NotParsed {
                    error_message,
                    position,
                }
            }
            ParseResult::NotParsedErrorPrinted {
                error_message,
                line,
                column,
            } => {
                return ParseResult::NotParsedErrorPrinted {
                    error_message,
                    line,
                    column,
                }
            }
        };

        $parser = advanced_parser;
    };
}

pub fn consume_list_impl<'a, 'b, T: Consume<'a, 'b> + std::fmt::Debug>(
    mut parser: Parser,
    data: &'b StaticParserData<'a>,
    end_token: TokenType,
    delimeter: TokenType,
    delimeter_terminated: bool,
) -> ParseResult<'a, Vec<T>> {
    let mut list = vec![];
    loop {
        if let ParseResult::Parsed(parser, ()) = parser.check_skip(data, end_token) {
            return parser.complete(list);
        }

        consume!(parser, data, T, t);
        list.push(t);

        match parser.first(data) {
            t if t.get_type() == delimeter => parser = parser.skip_one(),
            t if !delimeter_terminated && t.get_type() == end_token => {
                parser = parser.skip_one();
                return parser.complete(list);
            }
            t if delimeter_terminated => miss!(parser, "expected {delimeter:?}, found {t:?}"),
            t => miss!(
                parser,
                "expected {delimeter:?} or {end_token:?}, found {t:?}"
            ),
        }
    }
}

macro_rules! consume_list {
    ($parser:ident, $data:ident, $end_token:tt, $delimeter:tt, $delimeter_terminated:expr, $outvar:ident) => {
        let (advanced_parser, $outvar) = match consume_list_impl(
            $parser,
            $data,
            TokenType::$end_token,
            TokenType::$delimeter,
            $delimeter_terminated,
        ) {
            ParseResult::Parsed(parser, t) => {
                debug_assert_ne!($parser.current_position, parser.current_position);
                (parser, t)
            }
            ParseResult::NotParsed {
                error_message,
                position,
            } => {
                return ParseResult::NotParsed {
                    error_message,
                    position,
                }
            }
            ParseResult::NotParsedErrorPrinted {
                error_message,
                line,
                column,
            } => {
                return ParseResult::NotParsedErrorPrinted {
                    error_message,
                    line,
                    column,
                }
            }
        };

        $parser = advanced_parser;
    };
    ($parser:ident, $data:ident, $end_token:tt, $delimeter:tt, $outvar:ident) => {
        consume_list!($parser, $data, $end_token, $delimeter, false, $outvar)
    };
    ($parser:ident, $data:ident, $end_token:tt, $outvar:ident) => {
        consume_list!($parser, $data, $end_token, COMMA, false, $outvar)
    };
}

macro_rules! check {
    ($parser:ident, $data:ident, $token:tt) => {
        let advanced_parser = match $parser.check_skip($data, TokenType::$token) {
            ParseResult::Parsed(parser, _) => (parser),
            ParseResult::NotParsed {
                error_message,
                position,
            } => {
                return ParseResult::NotParsed {
                    error_message,
                    position,
                }
            }
            ParseResult::NotParsedErrorPrinted {
                error_message,
                line,
                column,
            } => {
                return ParseResult::NotParsedErrorPrinted {
                    error_message,
                    line,
                    column,
                }
            }
        };

        $parser = advanced_parser;
    };
}

macro_rules! localize_error {
    ($parser:ident, $data:ident, $ty:ty, $function_body:expr) => {{
        fn inner_func<'a>(
            mut $parser: Parser,
            $data: &StaticParserData<'a>,
        ) -> ParseResult<'a, $ty> {
            $function_body
        }

        match inner_func($parser, $data) {
            ParseResult::NotParsed {
                error_message,
                position,
            } if position != $parser.current_position => {
                let (line, column) = $parser.print_error($data, position);
                ParseResult::NotParsedErrorPrinted {
                    error_message,
                    line,
                    column,
                }
            }
            t => t,
        }
    }};
}

#[derive(Clone, Copy, PartialEq)]
pub(crate) struct Parser {
    pub(crate) current_position: usize,
}

pub(crate) struct StaticParserData<'a> {
    pub(crate) original_tokens: &'a [Token],
    pub(crate) string_map: &'a [&'a str],
    pub(crate) source: &'a str,
}

impl<'a, 'b> Parser {
    pub fn complete<T>(self, t: T) -> ParseResult<'a, T> {
        ParseResult::Parsed(self, t)
    }

    pub fn miss<T>(self, report: Box<dyn Fn() -> String + 'a>) -> ParseResult<'a, T> {
        ParseResult::NotParsed {
            error_message: report,
            position: self.current_position,
        }
    }

    #[must_use]
    pub fn skip_one(mut self) -> Self {
        self.current_position += 1;
        self
    }

    pub fn check_skip(
        self,
        data: &'b StaticParserData<'a>,
        token: TokenType,
    ) -> ParseResult<'a, ()> {
        debug_assert_ne!(token, TokenType::END_OF_FILE);
        if self.check_one(data, token) {
            ParseResult::Parsed(self.skip_one(), ())
        } else {
            let first = self.first(data);
            ParseResult::NotParsed {
                error_message: Box::new(move || format!("expected {token:?}, found {first:?}")),
                position: self.current_position,
            }
        }
    }

    pub fn check_one(self, data: &StaticParserData<'a>, token: TokenType) -> bool {
        self.first(data).get_type() == token
    }

    pub fn first(self, data: &StaticParserData<'a>) -> Token {
        debug_assert!(data.original_tokens.get(self.current_position).is_some());
        // SAFETY: EOF is always at the end and we never check for EOF
        unsafe { *data.original_tokens.get_unchecked(self.current_position) }
    }

    pub fn first_type(self, data: &StaticParserData<'a>) -> TokenType {
        self.first(data).get_type()
    }

    pub fn next(self, data: &StaticParserData<'a>) -> (Self, Token) {
        let next = self.first(data);
        (self.skip_one(), next)
    }

    pub fn next_type(self, data: &StaticParserData<'a>) -> (Self, TokenType) {
        let next = self.first_type(data);
        (self.skip_one(), next)
    }

    pub fn is_empty(self, data: &StaticParserData<'a>) -> bool {
        self.current_position == data.original_tokens.len()
    }

    /// This function prints the error token text in red and the surrounding text.
    pub fn print_error(
        &self,
        data: &'b StaticParserData<'a>,
        error_position: usize,
    ) -> (usize, usize) {
        let current_position = self.current_position;

        let input_by_token = input_by_token(data.source, data.original_tokens.len());

        let error_position = if error_position == input_by_token.len() {
            input_by_token.len() - 1
        } else {
            error_position
        };

        let [source_pre, semi_valid, error, source_post] = undo_slice_by_cuts(
            data.source,
            [
                UndoSliceSelection::Boundless,
                UndoSliceSelection::Beginning(input_by_token[current_position]),
                UndoSliceSelection::Beginning(input_by_token[error_position]),
                UndoSliceSelection::End(input_by_token[error_position]),
                UndoSliceSelection::Boundless,
            ],
        );

        let (source_pre, newlines) = {
            let mut src_iter = source_pre.split('\n').rev();

            let source_pre = src_iter
                .by_ref()
                .take(2)
                .map(|line| line.dimmed().to_string())
                .collect_vec()
                .iter()
                .rev()
                .join("\n");

            (source_pre, src_iter.count() + 1..)
        };

        // find the line and col of the error
        let (line, column) = {
            let mut line = 1;
            let mut column = 0;

            let start_ptr = data.source.as_ptr() as usize;
            let stop_ptr = input_by_token[error_position].as_ptr() as usize;

            for (i, c) in data.source.chars().enumerate() {
                if start_ptr + i == stop_ptr {
                    break;
                }

                if c == '\n' {
                    line += 1;
                    column = 0;
                } else {
                    column += 1;
                }
            }

            (line, column)
        };

        let semi_valid = semi_valid
            .split('\n')
            .map(|line| line.green().dimmed().to_string())
            .join("\n");

        let error = error
            .split('\n')
            .map(|line| line.red().to_string())
            .join("\n");

        let source_post = source_post
            .split('\n')
            .take(2)
            .map(|line| line.dimmed().to_string())
            .join("\n");

        let output = format!("{source_pre}{semi_valid}{error}{source_post}");
        let output = output
            .split('\n')
            .zip(newlines)
            .map(|(line, newline_count)| (newline_count, line))
            .collect_vec();

        let max_length_of_line_number = output
            .iter()
            .map(|(line_number, _)| line_number.to_string().len())
            .max()
            .unwrap();

        #[cfg(feature = "measure")]
        #[cfg(test)]
        return (line, column);

        for (line_number, line) in output {
            println!(
                "{}{line}",
                format!("{line_number:>max_length_of_line_number$} | ").bright_blue()
            );
        }
        println!();

        (line, column)
    }
}

pub(crate) use check;
pub(crate) use consume;
pub(crate) use consume_list;
pub(crate) use localize_error;
pub(crate) use miss;
