//! The module graph, and where an import points (LR21.1).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use luar_ast::Module;
use luar_diagnostics::{FileId, Span};

/// The extension a module file carries (LR2).
const EXTENSION: &str = "luar";

/// The module in scope everywhere without an import (LR54.1).
pub const PRELUDE: &str = "std/prelude";

/// What an import path names (LR21.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Specifier<'a> {
    /// `./config`, `../models/user`: a module beside the importing one.
    Relative(&'a str),
    /// `std/fs`: a module of the standard library.
    Std(&'a str),
    /// `http`, `some-package/router`: a package, and the module in it.
    Package {
        name: &'a str,
        /// The module inside the package, absent where the path names only
        /// the package.
        module: Option<&'a str>,
    },
}

/// What an import resolves to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Target {
    /// The file to read.
    File(PathBuf),
    /// No file, and why.
    Missing(Missing),
}

/// Why an import path names no file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Missing {
    /// The path is not one of the three forms LR21.1 states.
    Malformed,
    /// A standard library module, and there is no standard library to read
    /// it from yet.
    StandardLibrary,
    /// A package module, and packages are not resolved yet (LR22).
    Package,
}

/// Which of the three forms `path` is written in, or `None` where it is
/// none of them.
#[must_use]
pub fn classify(path: &str) -> Option<Specifier<'_>> {
    if path.is_empty() || path.ends_with('/') || path.contains('\\') || path.starts_with('/') {
        return None;
    }

    if path.starts_with("./") || path.starts_with("../") {
        return Some(Specifier::Relative(path));
    }

    if let Some(module) = path.strip_prefix("std/") {
        return Some(Specifier::Std(module));
    }

    let (name, module) = match path.split_once('/') {
        Some((name, module)) => (name, Some(module)),
        None => (path, None),
    };
    Some(Specifier::Package { name, module })
}

/// The file `path` names, imported from `importer`.
#[must_use]
pub fn resolve(path: &str, importer: &Path) -> Target {
    match classify(path) {
        None => Target::Missing(Missing::Malformed),
        Some(Specifier::Std(_)) => Target::Missing(Missing::StandardLibrary),
        Some(Specifier::Package { .. }) => Target::Missing(Missing::Package),
        Some(Specifier::Relative(path)) => {
            let directory = importer.parent().unwrap_or(Path::new(""));
            Target::File(normalize(directory.join(format!("{path}.{EXTENSION}"))))
        }
    }
}

/// Whether `path` is where the graph holds a standard library module: the
/// import path as written, which names no file (LR60).
#[must_use]
pub fn is_standard(path: &Path) -> bool {
    path.extension().is_none()
        && matches!(path.to_str().and_then(classify), Some(Specifier::Std(_)))
}

/// Resolves `.` and `..` in `path` without touching the filesystem.
#[must_use]
pub fn normalize(path: PathBuf) -> PathBuf {
    use std::path::Component;

    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir if out.components().next_back().is_some_and(is_name) => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out
}

fn is_name(component: std::path::Component<'_>) -> bool {
    matches!(component, std::path::Component::Normal(_))
}

/// A module in the graph. Stable for the life of the [`Graph`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleId(u32);

/// One resolved package identity (LR22).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackageId(u32);

/// The name and resolved source identity of a package (LR22).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Package {
    pub name: String,
    pub version: String,
    pub source: PathBuf,
}

/// One module: its source, its syntax, and what it imports.
#[derive(Debug)]
pub struct Node {
    pub file: FileId,
    /// The file it was read from, resolved. Two imports naming this module
    /// spell it the same way, so the graph holds it once (LR21.2).
    pub path: PathBuf,
    pub package: PackageId,
    pub ast: Module,
    /// One edge per import, in the order written.
    pub imports: Vec<Edge>,
    /// The prelude this module sees without an import (LR54.1). Absent in
    /// the prelude and in the modules it reaches.
    pub prelude: Option<ModuleId>,
}

/// An import, and the module it reached.
#[derive(Debug, Clone, Copy)]
pub struct Edge {
    /// The module imported. Absent where the import resolved to nothing,
    /// which is reported where it is found.
    pub target: Option<ModuleId>,
    /// The path as written, for pointing at.
    pub span: Span,
}

/// Every module one compilation reaches, and the imports between them (LR21.1).
#[derive(Debug)]
pub struct Graph {
    nodes: Vec<Node>,
    by_path: BTreeMap<PathBuf, ModuleId>,
    packages: Vec<Package>,
}

impl Default for Graph {
    fn default() -> Self {
        Self {
            nodes: Vec::new(),
            by_path: BTreeMap::new(),
            packages: vec![Package {
                name: String::new(),
                version: String::new(),
                source: PathBuf::new(),
            }],
        }
    }
}

impl Graph {
    /// The module compilation started from.
    #[must_use]
    pub fn root(&self) -> ModuleId {
        ModuleId(0)
    }

    /// Adds a module read from `path`, and returns its id.
    ///
    /// # Panics
    pub fn insert(
        &mut self,
        file: FileId,
        path: PathBuf,
        package: PackageId,
        ast: Module,
    ) -> ModuleId {
        let id = ModuleId(u32::try_from(self.nodes.len()).expect("module count fits in u32"));
        assert!(
            self.by_path.insert(path.clone(), id).is_none(),
            "one module per file: {}",
            path.display()
        );
        self.nodes.push(Node {
            file,
            path,
            package,
            ast,
            imports: Vec::new(),
            prelude: None,
        });
        id
    }

    /// The identity used by source files outside a package.
    #[must_use]
    pub fn loose_package(&self) -> PackageId {
        PackageId(0)
    }

    /// Records one resolved package identity (LR22).
    pub fn add_package(&mut self, package: Package) -> PackageId {
        let id = PackageId(u32::try_from(self.packages.len()).expect("package count fits in u32"));
        self.packages.push(package);
        id
    }

    /// A resolved package identity (LR22).
    #[must_use]
    pub fn package(&self, id: PackageId) -> &Package {
        self.packages
            .get(id.0 as usize)
            .expect("package id belongs to another graph")
    }

    /// The prelude, once it is in the graph (LR54.1).
    #[must_use]
    pub fn prelude(&self) -> Option<ModuleId> {
        self.find(Path::new(PRELUDE))
    }

    /// Puts `prelude` in scope in every module it does not reach, itself
    /// included (LR54.1). Called once every import is recorded.
    pub fn open_prelude(&mut self, prelude: ModuleId) {
        let mut reached = BTreeSet::from([prelude]);
        let mut pending = vec![prelude];
        while let Some(id) = pending.pop() {
            for target in self
                .module(id)
                .imports
                .iter()
                .filter_map(|edge| edge.target)
            {
                if reached.insert(target) {
                    pending.push(target);
                }
            }
        }

        for (id, node) in self.nodes.iter_mut().enumerate() {
            if !reached.contains(&ModuleId(id as u32)) {
                node.prelude = Some(prelude);
            }
        }
    }

    /// The module read from `path`, if it is already in the graph.
    #[must_use]
    pub fn find(&self, path: &Path) -> Option<ModuleId> {
        self.by_path.get(path).copied()
    }

    /// Records what `id` imports, once every module it names is in the graph.
    ///
    /// # Panics
    pub fn set_imports(&mut self, id: ModuleId, imports: Vec<Edge>) {
        self.node_mut(id).imports = imports;
    }

    /// # Panics
    #[must_use]
    pub fn module(&self, id: ModuleId) -> &Node {
        self.nodes
            .get(id.0 as usize)
            .expect("module id belongs to another graph")
    }

    /// # Panics
    pub fn module_mut(&mut self, id: ModuleId) -> &mut Node {
        self.node_mut(id)
    }

    /// Every module, in the order they were discovered.
    pub fn modules(&self) -> impl Iterator<Item = (ModuleId, &Node)> {
        self.nodes
            .iter()
            .enumerate()
            .map(|(i, node)| (ModuleId(i as u32), node))
    }

    fn node_mut(&mut self, id: ModuleId) -> &mut Node {
        self.nodes
            .get_mut(id.0 as usize)
            .expect("module id belongs to another graph")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_leading_dot_is_what_makes_a_path_relative() {
        assert_eq!(classify("./config"), Some(Specifier::Relative("./config")));
        assert_eq!(
            classify("../models/user"),
            Some(Specifier::Relative("../models/user"))
        );
    }

    #[test]
    fn std_names_the_standard_library_and_not_a_package_called_std() {
        assert_eq!(classify("std/fs"), Some(Specifier::Std("fs")));
        assert_eq!(
            classify("std"),
            Some(Specifier::Package {
                name: "std",
                module: None
            })
        );
    }

    #[test]
    fn a_package_path_splits_at_the_first_slash() {
        assert_eq!(
            classify("some-package/router"),
            Some(Specifier::Package {
                name: "some-package",
                module: Some("router")
            })
        );
        assert_eq!(
            classify("http"),
            Some(Specifier::Package {
                name: "http",
                module: None
            })
        );
    }

    #[test]
    fn a_path_that_names_no_module_is_not_one_of_the_forms() {
        assert_eq!(classify(""), None);
        assert_eq!(classify("./"), None);
        assert_eq!(classify("/etc/passwd"), None);
        assert_eq!(classify(".\\config"), None);
    }

    #[test]
    fn a_relative_import_resolves_beside_the_importing_file() {
        let importer = Path::new("src/app.luar");
        assert_eq!(
            resolve("./config", importer),
            Target::File(PathBuf::from("src/config.luar"))
        );
        assert_eq!(
            resolve("../models/user", importer),
            Target::File(PathBuf::from("models/user.luar"))
        );
    }

    #[test]
    fn one_module_reached_two_ways_is_one_path() {
        assert_eq!(
            resolve("./sub/../shared", Path::new("src/app.luar")),
            resolve("./shared", Path::new("src/app.luar"))
        );
    }

    #[test]
    fn a_module_name_with_a_dot_in_it_keeps_it() {
        assert_eq!(
            resolve("./config.v2", Path::new("app.luar")),
            Target::File(PathBuf::from("config.v2.luar"))
        );
    }

    #[test]
    fn climbing_past_the_root_of_a_relative_path_is_kept() {
        assert_eq!(
            resolve("../../shared", Path::new("app.luar")),
            Target::File(PathBuf::from("../../shared.luar"))
        );
    }

    #[test]
    fn what_cannot_be_resolved_yet_says_which_it_is() {
        let importer = Path::new("app.luar");
        assert_eq!(
            resolve("std/fs", importer),
            Target::Missing(Missing::StandardLibrary)
        );
        assert_eq!(
            resolve("some-package/router", importer),
            Target::Missing(Missing::Package)
        );
        assert_eq!(resolve("", importer), Target::Missing(Missing::Malformed));
    }
}
