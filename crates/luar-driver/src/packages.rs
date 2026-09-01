//! Filesystem package metadata and dependency resolution (LR22).

use std::collections::BTreeMap;
use std::fs;
use std::path::{Component, Path, PathBuf};

use luar_sema::modules::{Graph, Package, PackageId};

const MANIFEST: &str = "luar.toml";

#[derive(Debug)]
struct Metadata {
    name: String,
    version: String,
    source: PathBuf,
    modules: PathBuf,
    main: String,
    dependencies: BTreeMap<String, PathBuf>,
}

#[derive(Debug, Default)]
pub(crate) struct Packages {
    loaded: BTreeMap<PackageId, Metadata>,
    by_source: BTreeMap<PathBuf, PackageId>,
}

impl Packages {
    pub(crate) fn root(&mut self, graph: &mut Graph, source: &Path) -> Result<PackageId, String> {
        let Some(directory) = manifest_ancestor(source) else {
            return Ok(graph.loose_package());
        };
        self.load(graph, &directory)
    }

    pub(crate) fn resolve(
        &mut self,
        graph: &mut Graph,
        importer: PackageId,
        name: &str,
        module: Option<&str>,
    ) -> Result<(PathBuf, PackageId), String> {
        let package = self
            .loaded
            .get(&importer)
            .ok_or_else(|| format!("`{name}` is not declared by a package manifest"))?;
        let source = package
            .dependencies
            .get(name)
            .cloned()
            .ok_or_else(|| format!("`{name}` is not a dependency of `{}`", package.name))?;

        let target = self.load(graph, &source)?;
        let package = self
            .loaded
            .get(&target)
            .expect("a loaded package has metadata");
        if package.name != name {
            return Err(format!(
                "dependency `{name}` resolves to package `{}`",
                package.name
            ));
        }

        let module = module.unwrap_or(&package.main);
        if !module_path(module) {
            return Err(format!("`{name}/{module}` does not name a package module"));
        }

        Ok((package.modules.join(module).with_extension("luar"), target))
    }

    fn load(&mut self, graph: &mut Graph, source: &Path) -> Result<PackageId, String> {
        let source = fs::canonicalize(source).map_err(|error| {
            format!(
                "package source `{}` could not be read: {error}",
                source.display()
            )
        })?;
        if let Some(id) = self.by_source.get(&source) {
            return Ok(*id);
        }

        let metadata = read(&source)?;
        let id = graph.add_package(Package {
            name: metadata.name.clone(),
            version: metadata.version.clone(),
            source: metadata.source.clone(),
        });
        self.by_source.insert(source, id);
        self.loaded.insert(id, metadata);
        Ok(id)
    }
}

fn manifest_ancestor(source: &Path) -> Option<PathBuf> {
    source.parent()?.ancestors().find_map(|directory| {
        directory
            .join(MANIFEST)
            .is_file()
            .then(|| directory.to_path_buf())
    })
}

fn read(source: &Path) -> Result<Metadata, String> {
    let manifest = source.join(MANIFEST);
    let text = fs::read_to_string(&manifest)
        .map_err(|error| format!("`{}` could not be read: {error}", manifest.display()))?;
    let value: toml::Value = toml::from_str(&text)
        .map_err(|error| format!("`{}` is not valid TOML: {error}", manifest.display()))?;

    let package = value
        .get("package")
        .and_then(toml::Value::as_table)
        .ok_or_else(|| format!("`{}` has no `[package]` table", manifest.display()))?;
    let name = string(package, "name", &manifest)?;
    let version = string(package, "version", &manifest)?;
    let root = optional_string(package, "root", "src", &manifest)?;
    let main = optional_string(package, "main", "lib", &manifest)?;
    if !module_path(&main) {
        return Err(format!(
            "`package.main` in `{}` is not a module path",
            manifest.display()
        ));
    }

    let mut dependencies = BTreeMap::new();
    if let Some(table) = value.get("dependencies").and_then(toml::Value::as_table) {
        for (name, value) in table {
            let path = value.as_str().ok_or_else(|| {
                format!(
                    "dependency `{name}` in `{}` is not a path string",
                    manifest.display()
                )
            })?;
            dependencies.insert(name.clone(), source.join(path));
        }
    }

    Ok(Metadata {
        name,
        version,
        source: source.to_path_buf(),
        modules: source.join(root),
        main,
        dependencies,
    })
}

fn string(table: &toml::Table, name: &str, manifest: &Path) -> Result<String, String> {
    table
        .get(name)
        .and_then(toml::Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| format!("`package.{name}` is missing from `{}`", manifest.display()))
}

fn optional_string(
    table: &toml::Table,
    name: &str,
    default: &str,
    manifest: &Path,
) -> Result<String, String> {
    match table.get(name) {
        Some(value) => value.as_str().map(str::to_owned).ok_or_else(|| {
            format!(
                "`package.{name}` in `{}` is not a string",
                manifest.display()
            )
        }),
        None => Ok(default.to_owned()),
    }
}

fn module_path(path: &str) -> bool {
    !path.is_empty()
        && Path::new(path)
            .components()
            .all(|component| matches!(component, Component::Normal(_)))
}
