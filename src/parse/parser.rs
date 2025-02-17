use colored::Colorize;
use itertools::Itertools;

use crate::{
    lex::{input_by_token, InputByToken, Token, TokenType},
    undo_slice_by_cuts, UndoSliceSelection,
};

pub(crate) trait Consume<'a, 'b>: Sized {
    fn consume(parser: Parser, ctx: &'b ParserContext<'a>) -> ParseResult<'a, Self>;
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
    Parsed(Parser, T, SourceInfo),
}

impl<'a, T> ParseResult<'a, T> {
    pub fn erase<O>(self) -> ParseResult<'a, O> {
        match self {
            ParseResult::NotParsedErrorPrinted {
                error_message,
                line,
                column,
            } => ParseResult::NotParsedErrorPrinted {
                error_message,
                line,
                column,
            },
            ParseResult::NotParsed {
                error_message,
                position,
            } => ParseResult::NotParsed {
                error_message,
                position,
            },
            ParseResult::Parsed(..) => panic!(),
        }
    }
}

macro_rules! miss {
    ($parser:ident, $($msg:tt)*) => {
        return $parser.miss(Box::new(move || format!($($msg)*)))
    };
}

macro_rules! consume {
    ($parser:ident, $ctx:ident, $type:ty, $outvar:ident) => {
        let (advanced_parser, $outvar, source_info) = match <$type>::consume($parser, $ctx) {
            ParseResult::Parsed(parser, t, source_info) => {
                debug_assert_ne!($parser.current_position, parser.current_position);
                (parser, t, source_info)
            }
            pr => return pr.erase(),
        };

        $parser = advanced_parser;

        source_info
    };
}

pub fn consume_list_impl<'a, 'b, T: Consume<'a, 'b> + std::fmt::Debug>(
    mut parser: Parser,
    ctx: &'b ParserContext<'a>,
    end_token: TokenType,
    delimeter: TokenType,
    delimeter_terminated: bool,
) -> ParseResult<'a, Vec<T>> {
    let mut list = vec![];

    let range = SourceInfo::mark_range(&parser);

    loop {
        if let ParseResult::Parsed(parser, (), _) = parser.check_skip(ctx, end_token) {
            return parser.complete_range(list, &range);
        }

        consume!(parser, ctx, T, t);
        list.push(t);

        match parser.first(ctx) {
            (t, _) if t.get_type() == delimeter => parser = parser.skip_one(),
            (t, _) if !delimeter_terminated && t.get_type() == end_token => {
                return parser.skip_one().complete_range(list, &range);
            }
            (t, _) if delimeter_terminated => miss!(parser, "expected {delimeter:?}, found {t:?}"),
            (t, _) => miss!(
                parser,
                "expected {delimeter:?} or {end_token:?}, found {t:?}"
            ),
        }
    }
}

macro_rules! consume_list {
    ($parser:ident, $ctx:ident, $end_token:tt, $delimeter:tt, $delimeter_terminated:expr, $outvar:ident) => {
        let (advanced_parser, $outvar) = match consume_list_impl(
            $parser,
            $ctx,
            TokenType::$end_token,
            TokenType::$delimeter,
            $delimeter_terminated,
        ) {
            ParseResult::Parsed(parser, t, _) => {
                debug_assert_ne!($parser.current_position, parser.current_position);
                (parser, t)
            }
            pr => return pr.erase(),
        };

        $parser = advanced_parser;
    };
    ($parser:ident, $ctx:ident, $end_token:tt, $delimeter:tt, $outvar:ident) => {
        consume_list!($parser, $ctx, $end_token, $delimeter, false, $outvar)
    };
    ($parser:ident, $ctx:ident, $end_token:tt, $outvar:ident) => {
        consume_list!($parser, $ctx, $end_token, COMMA, false, $outvar)
    };
}

macro_rules! check {
    ($parser:ident, $ctx:ident, $token:tt) => {
        let (advanced_parser, source_info) = match $parser.check_skip($ctx, TokenType::$token) {
            ParseResult::Parsed(parser, _, source_info) => (parser, source_info),
            pr => return pr.erase(),
        };

        $parser = advanced_parser;

        source_info
    };
}

macro_rules! localize_error {
    ($parser:ident, $ctx:ident, $ty:ty, $function_body:expr) => {{
        fn inner_func<'a>(mut $parser: Parser, $ctx: &ParserContext<'a>) -> ParseResult<'a, $ty> {
            $function_body
        }

        match inner_func($parser, $ctx) {
            ParseResult::NotParsed {
                error_message,
                position,
            } if position != $parser.current_position => {
                let (line, column) = $parser.print_error($ctx, position);
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

pub(crate) struct ParserContext<'a> {
    pub(crate) original_tokens: &'a [Token],
    pub(crate) string_map: &'a [&'a str],
    pub(crate) source: &'a str,
}

impl<'a, 'b> Parser {
    pub fn complete<T>(self, t: T, total_source_slice: SourceInfo) -> ParseResult<'a, T> {
        ParseResult::Parsed(self, t, total_source_slice)
    }

    pub fn complete_range<T>(self, t: T, range: &SourceInfoMarker) -> ParseResult<'a, T> {
        debug_assert_ne!(range.start_index, self.current_position);
        let range = SourceInfo::Range(range.start_index, self.current_position);
        ParseResult::Parsed(self, t, range)
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

    pub fn check_skip(self, ctx: &'b ParserContext<'a>, token: TokenType) -> ParseResult<'a, ()> {
        debug_assert_ne!(token, TokenType::END_OF_FILE);
        if let Some(slice) = self.check_one(ctx, token) {
            ParseResult::Parsed(self.skip_one(), (), slice)
        } else {
            let first = self.first(ctx);
            ParseResult::NotParsed {
                error_message: Box::new(move || format!("expected {token:?}, found {first:?}")),
                position: self.current_position,
            }
        }
    }

    pub fn check_one(self, ctx: &ParserContext<'a>, token: TokenType) -> Option<SourceInfo> {
        let first = self.first(ctx);
        (first.0.get_type() == token).then_some(first.1)
    }

    pub fn first(self, ctx: &ParserContext<'a>) -> (Token, SourceInfo) {
        debug_assert!(ctx.original_tokens.get(self.current_position).is_some());
        // SAFETY: EOF is always at the end and we never check for EOF
        let next = unsafe { *ctx.original_tokens.get_unchecked(self.current_position) };

        (next, SourceInfo::Token(self.current_position))
    }

    pub fn first_type(self, ctx: &ParserContext<'a>) -> TokenType {
        self.first(ctx).0.get_type()
    }

    pub fn next(self, ctx: &ParserContext<'a>) -> (Self, Token, SourceInfo) {
        let (next, slice) = self.first(ctx);
        (self.skip_one(), next, slice)
    }

    pub fn next_type(self, ctx: &ParserContext<'a>) -> (Self, TokenType) {
        (self.skip_one(), self.first_type(ctx))
    }

    pub fn is_empty(self, ctx: &ParserContext<'a>) -> bool {
        self.current_position == ctx.original_tokens.len()
    }

    /// This function prints the error token text in red and the surrounding text.
    pub fn print_error(&self, ctx: &'b ParserContext<'a>, error_position: usize) -> (usize, usize) {
        let current_position = self.current_position;

        let InputByToken(input_by_token) = input_by_token(ctx.source, ctx.original_tokens.len());

        let error_position = if error_position == input_by_token.len() {
            input_by_token.len() - 1
        } else {
            error_position
        };

        let [source_pre, semi_valid, error, source_post] = undo_slice_by_cuts(
            ctx.source,
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

            let start_ptr = ctx.source.as_ptr() as usize;
            let stop_ptr = input_by_token[error_position].as_ptr() as usize;

            for (i, c) in ctx.source.chars().enumerate() {
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

#[derive(Debug, Clone, Copy)]
pub enum SourceInfo {
    Token(usize),
    Range(usize, usize),
    // Syntax,
    Builtin,
}

impl SourceInfo {
    /// # Panics
    #[must_use]
    pub fn unwrap_token_index(self) -> usize {
        match self {
            SourceInfo::Token(t) => t,
            _ => panic!("Expected token, found {self:?}"),
        }
    }

    #[must_use]
    pub fn mark_range(parser: &Parser) -> SourceInfoMarker {
        SourceInfoMarker {
            start_index: parser.current_position,
        }
    }

    // pub fn get_string<'a>(&self, input_by_token: &InputByToken<'a>) -> &'a str {
    //     input_by_token.0[self.0]
    // }
}

pub struct SourceInfoMarker {
    start_index: usize,
}
