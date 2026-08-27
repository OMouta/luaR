//! Initialization order, and the cycles that have none (LR21.2, LR78).

use std::collections::BTreeMap;

use luar_diagnostics::{Diagnostic, Span, codes};

use crate::modules::{Graph, ModuleId};

/// A name another module owns, read while this one initializes.
#[derive(Debug, Clone, Copy)]
pub struct Use {
    /// The module running its top-level code.
    pub module: ModuleId,
    /// The module that has to be initialized for the read to be valid.
    pub needs: ModuleId,
    /// Where the name was read.
    pub span: Span,
}

/// Reports every cycle of modules that cannot be ordered.
#[must_use]
pub fn check(graph: &Graph, uses: &[Use]) -> Vec<Diagnostic> {
    let mut needs: BTreeMap<ModuleId, Vec<(ModuleId, Span)>> = BTreeMap::new();

    for use_ in uses {
        // A module needing itself is the module it is already in, and one need
        // per pair is enough to order them.
        let edges = needs.entry(use_.module).or_default();
        if use_.module != use_.needs && !edges.iter().any(|(to, _)| *to == use_.needs) {
            edges.push((use_.needs, use_.span));
        }
    }

    let mut walk = Walk {
        graph,
        needs: &needs,
        state: BTreeMap::new(),
        path: Vec::new(),
        diagnostics: Vec::new(),
    };

    for (id, _) in graph.modules() {
        walk.visit(id);
    }

    walk.diagnostics
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    /// On the path being walked. Reaching it again closes a cycle.
    Open,
    Done,
}

struct Walk<'a> {
    graph: &'a Graph,
    needs: &'a BTreeMap<ModuleId, Vec<(ModuleId, Span)>>,
    state: BTreeMap<ModuleId, State>,
    /// The modules being walked, each with the read that led to the next.
    path: Vec<(ModuleId, Span)>,
    diagnostics: Vec<Diagnostic>,
}

impl Walk<'_> {
    fn visit(&mut self, module: ModuleId) {
        if self.state.contains_key(&module) {
            return;
        }
        self.state.insert(module, State::Open);

        let edges: Vec<(ModuleId, Span)> = self
            .needs
            .get(&module)
            .map(|edges| edges.to_vec())
            .unwrap_or_default();

        for (needed, span) in edges {
            match self.state.get(&needed) {
                Some(State::Open) => self.report(module, needed, span),
                Some(State::Done) => {}
                None => {
                    self.path.push((module, span));
                    self.visit(needed);
                    self.path.pop();
                }
            }
        }

        self.state.insert(module, State::Done);
    }

    /// Reports the cycle that reading from `needed` inside `module` closes.
    fn report(&mut self, module: ModuleId, needed: ModuleId, span: Span) {
        let start = self
            .path
            .iter()
            .position(|(walked, _)| *walked == needed)
            .expect("the module reached again is on the path");

        let mut cycle: Vec<(ModuleId, Span)> = self.path[start..].to_vec();
        cycle.push((module, span));

        // The cycle is reported where it opens, so the primary span is in the
        // module the walk reached first rather than wherever it closed.
        let (first, opens) = cycle[0];
        let mut diagnostic = Diagnostic::error(
            codes::UNSAFE_IMPORT_CYCLE,
            opens,
            format!(
                "initializing `{}` reads from `{}`, which needs `{}` back",
                self.name(first),
                self.name(cycle[1].0),
                self.name(first)
            ),
        );

        for (module, span) in &cycle[1..] {
            diagnostic = diagnostic.label(
                *span,
                format!("`{}` reads this while it initializes", self.name(*module)),
            );
        }

        self.diagnostics.push(diagnostic.note(
            "Modules in a cycle are ordered by what their top-level code reads. \
             Reading it inside a function instead leaves the cycle orderable (LR21.2, LR78).",
        ));
    }

    fn name(&self, module: ModuleId) -> String {
        self.graph.module(module).path.display().to_string()
    }
}
