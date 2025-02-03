use std::path::Path;

use rjplc::lex::LexImplementation;
use rjplc::{lex, parse};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct Output {
    lex_output: Option<String>,
    parse_output: Option<String>,
    type_check_output: Option<String>,
}

#[wasm_bindgen]
impl Output {
    #[wasm_bindgen(getter)]
    pub fn lex_output(&self) -> Option<String> {
        self.lex_output.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn parse_output(&self) -> Option<String> {
        self.parse_output.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn type_check_output(&self) -> Option<String> {
        self.type_check_output.clone()
    }
}

#[wasm_bindgen]
pub fn perform_steps(contents: &str) -> Output {
    let mut successful_steps = Output {
        lex_output: None,
        parse_output: None,
        type_check_output: None,
    };

    let (tokens, input_by_token) = match lex::LexLinear::lex(contents) {
        Ok(tokens) => tokens,
        Err(e) => {
            successful_steps.lex_output = Some(format!("{e}"));
            successful_steps.parse_output = Some("Lexing failed, cannot parse".to_string());
            return successful_steps;
        }
    };

    use std::fmt::Write;
    let mut output = String::new();

    for token in &tokens {
        writeln!(output, "{token}").unwrap();
    }

    successful_steps.lex_output = Some(output);

    let parsed = match parse::parse(&tokens, &input_by_token, contents, Path::new("textarea")) {
        Ok(parsed) => parsed,
        Err(e) => {
            successful_steps.parse_output = Some(format!("{e}"));
            return successful_steps;
        }
    };

    let mut output = String::new();

    for parsed in parsed {
        writeln!(output, "{parsed}").unwrap();
    }

    successful_steps.parse_output = Some(output);

    successful_steps
}
