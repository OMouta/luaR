//! Test discovery and executable construction (LR61).

use std::path::Path;

use luar_ast::Item;
use luar_diagnostics::{FileId, SourceMap};
use luar_lir::lower::Lowered;
use luar_lir::{FuncId, Program};
use luar_parser::Target;

use crate::{BuildError, CompilationMode};

pub struct Test {
    pub name: String,
    entry: FuncId,
}

pub struct Suite {
    pub tests: Vec<Test>,
    program: Program,
}

pub fn collect(sources: &mut SourceMap, root: FileId) -> Result<Suite, BuildError> {
    let checked = crate::frontend(sources, root, Target::host(true));
    let declarations: Vec<_> = checked
        .graph
        .module(checked.graph.root())
        .ast
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function)
                if function
                    .decorators
                    .iter()
                    .any(|decorator| decorator.name == "test") =>
            {
                Some((function.name.join("."), function.span))
            }
            _ => None,
        })
        .collect();
    let lowered =
        crate::lower_checked(checked, CompilationMode::Debug).map_err(BuildError::Rejected)?;
    if !lowered.gaps.is_empty() {
        return Err(BuildError::NotLowered(lowered.gaps));
    }
    let tests = declarations
        .into_iter()
        .map(|(name, span)| {
            let entry = lowered
                .program
                .functions()
                .find(|(_, function)| function.span == span)
                .map(|(id, _)| id)
                .expect("a checked test has a lowered function");
            Test { name, entry }
        })
        .collect();
    Ok(Suite {
        tests,
        program: lowered.program,
    })
}

impl Suite {
    pub fn build(&self, test: &Test, output: &Path) -> Result<(), BuildError> {
        let mut lowered = Lowered {
            program: self.program.clone(),
            gaps: Vec::new(),
        };
        lowered.program.entry = Some(test.entry);
        crate::finish_lowering(&mut lowered);
        crate::build_lowered(&lowered, output)
    }
}
