use std::path::Path;

use rjplc::{lex, parse, CustomDisplay};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct Output {
    lex_output: Option<String>,
    pub lex_success: bool,
    parse_output: Option<String>,
    pub parse_success: bool,
    type_check_output: Option<String>,
    pub type_check_success: bool,
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
    console_error_panic_hook::set_once();

    let mut successful_steps = Output {
        lex_output: None,
        lex_success: false,
        parse_output: None,
        parse_success: false,
        type_check_output: None,
        type_check_success: false,
    };

    let (tokens, input_by_token, string_map) = match lex::lex(contents) {
        Ok(tokens) => tokens,
        Err(e) => {
            successful_steps.lex_output = Some(format!("{e}"));
            successful_steps.parse_output = Some("Lexing failed, cannot parse".to_string());
            return successful_steps;
        }
    };

    successful_steps.lex_success = true;

    let mut output = String::new();

    for token in &tokens {
        token
            .fmt(&mut output, &string_map)
            .expect("writing should always work");
        output.push('\n');
    }

    successful_steps.lex_output = Some(output);

    let parsed = match parse::parse(
        &tokens,
        &input_by_token,
        &string_map,
        contents,
        Path::new("textarea"),
    ) {
        Ok(parsed) => parsed,
        Err(e) => {
            successful_steps.parse_output = Some(format!("{e}"));
            return successful_steps;
        }
    };

    successful_steps.parse_success = true;

    let mut output = String::new();

    for parsed in parsed {
        parsed
            .fmt(&mut output, &string_map)
            .expect("writing should always work");
        output.push('\n');
    }

    successful_steps.parse_output = Some(output);

    successful_steps
}
