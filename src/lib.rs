#![deny(clippy::pedantic)]
#![allow(clippy::cast_possible_truncation)]

use std::cell::Cell;

use std::{
    fs,
    path::{Path, PathBuf},
};

use itertools::Itertools;

pub mod lex;
pub mod measure;
pub mod parse;
pub mod typecheck;

#[derive(Debug, Clone, Copy)]
enum UndoSliceSelection<'a> {
    Boundless,
    Beginning(&'a str),
    End(&'a str),
}

fn undo_slice<'a>(
    original: &'a str,
    a: UndoSliceSelection<'a>,
    b: UndoSliceSelection<'a>,
) -> &'a str {
    fn resolve_idx(
        original: &'_ str,
        undo_selection: UndoSliceSelection<'_>,
        default: usize,
    ) -> usize {
        match undo_selection {
            UndoSliceSelection::Beginning(undo_selection) => {
                undo_selection.as_ptr() as usize - original.as_ptr() as usize
            }
            UndoSliceSelection::End(undo_selection) => {
                undo_selection.as_ptr() as usize + undo_selection.len() - original.as_ptr() as usize
            }
            UndoSliceSelection::Boundless => default,
        }
    }

    let start = resolve_idx(original, a, 0);
    let end = resolve_idx(original, b, original.len());

    assert!(start <= end);

    &original[start..end]
}

#[test]
fn test_undo_slice() {
    let original = "hello world";
    assert_eq!(
        undo_slice(
            original,
            UndoSliceSelection::Boundless,
            UndoSliceSelection::Boundless
        ),
        original
    );

    let slice = &original[1..4];

    assert_eq!(
        undo_slice(
            original,
            UndoSliceSelection::Boundless,
            UndoSliceSelection::End(slice)
        ),
        "hell"
    );

    let slice = &original[1..4];

    assert_eq!(
        undo_slice(
            original,
            UndoSliceSelection::Beginning(slice),
            UndoSliceSelection::End(slice)
        ),
        "ell"
    );

    let slice = &original[1..4];

    assert_eq!(
        undo_slice(
            original,
            UndoSliceSelection::Boundless,
            UndoSliceSelection::Beginning(slice),
        ),
        "h"
    );
}

fn undo_slice_by_cuts<'a, const N: usize, const M: usize>(
    original: &'a str,
    cuts: [UndoSliceSelection<'a>; N],
) -> [&'a str; M] {
    const {
        assert!(N - 1 == M);
    }

    cuts.iter()
        .tuple_windows()
        .map(|(a, b)| undo_slice(original, *a, *b))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

/// # Panics
pub fn test_correct(directory: &str, mut tester: impl FnMut(&str, &str)) {
    let (all_test_paths, all_solution_paths) = prepare_test_correct(directory);
    for (test_path, solution_path) in all_test_paths.iter().zip(all_solution_paths.iter()) {
        #[cfg(not(feature = "measure"))]
        println!("{}", test_path.display());
        #[cfg(not(feature = "measure"))]
        println!("{}", solution_path.display());
        let file = fs::read_to_string(test_path).unwrap();
        let solution_file = fs::read_to_string(solution_path).unwrap();

        #[cfg(not(feature = "measure"))]
        println!("{file}");

        tester(&file, &solution_file);
    }
}

#[must_use]
pub fn prepare_test_correct(directory: &str) -> (Vec<PathBuf>, Vec<PathBuf>) {
    let all_test_paths = get_test_paths(directory);
    let mut all_solution_paths = vec![];

    for test_path in &all_test_paths {
        let mut solution_path = test_path.clone();
        // add .expected to the end of the path
        solution_path.set_extension("jpl.expected");

        all_solution_paths.push(solution_path);
    }

    (all_test_paths, all_solution_paths)
}

pub fn test_solos(directory: &str, mut tester: impl FnMut(&str, &std::path::Path)) {
    for test_path in get_test_paths(directory) {
        #[cfg(not(feature = "measure"))]
        println!("{}", test_path.display());
        if let Ok(file) = fs::read_to_string(&test_path) {
            tester(&file, &test_path);
        }
    }
}

/// # Panics
#[must_use]
pub fn get_test_paths(directory: &str) -> Vec<PathBuf> {
    let folder = Path::new(directory);
    assert!(folder.exists(), "Could not find {}", folder.display());

    fs::read_dir(folder)
        .unwrap()
        .flatten()
        .filter(|f| f.file_type().unwrap().is_file())
        .filter(|f| f.path().extension().unwrap() == "jpl")
        .map(|f| f.path())
        .collect_vec()
}

pub trait CustomDisplay {
    /// # Errors
    /// Normal `std::fmt::Result` error conditions on writes.
    fn fmt(&self, f: &mut String, string_map: &[&str]) -> std::fmt::Result;
}

thread_local! {
    static PRINT_TYPES: Cell<bool> = const { Cell::new(false) };
}
