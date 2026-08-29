//! Which spec sections have tests, and which do not.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;

use crate::{directives, discover};

/// A language or standard-library section such as `LR11.1` or `STD5`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Section {
    prefix: String,
    number: String,
}

impl Section {
    /// Reads a section from a citation. A bare number belongs to the language
    /// specification.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        let text = text.trim();
        let (prefix, text) = if let Some(text) = text.strip_prefix("STD") {
            ("STD", text)
        } else if let Some(text) = text.strip_prefix("LR") {
            ("LR", text)
        } else {
            ("LR", text)
        };
        Self::with_prefix(prefix, text)
    }

    fn with_prefix(prefix: &str, text: &str) -> Option<Self> {
        let text = text.trim();
        let number: String = text
            .chars()
            .take_while(|c| c.is_ascii_digit() || *c == '.')
            .collect();
        let number = number.trim_end_matches('.');

        if number.is_empty() || !number.starts_with(|c: char| c.is_ascii_digit()) {
            return None;
        }
        if number.split('.').any(|part| part.is_empty()) {
            return None;
        }
        Some(Self {
            prefix: prefix.to_owned(),
            number: number.to_owned(),
        })
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.number
    }

    /// The sections this one sits inside: `11.1.2` yields `11.1` and `11`.
    fn ancestors(&self) -> impl Iterator<Item = Self> + '_ {
        self.number.match_indices('.').map(|(i, _)| Self {
            prefix: self.prefix.clone(),
            number: self.number[..i].to_owned(),
        })
    }

    /// Orders `11.2` before `11.10`, which string order gets wrong.
    fn key(&self) -> Vec<u32> {
        self.number
            .split('.')
            .map(|p| p.parse().unwrap_or(0))
            .collect()
    }
}

impl fmt::Display for Section {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.prefix, self.number)
    }
}

impl PartialOrd for Section {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Section {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.prefix
            .cmp(&other.prefix)
            .then_with(|| self.key().cmp(&other.key()))
    }
}

/// Every numbered heading in a Markdown specification, in document order.
#[must_use]
pub fn sections(markdown: &str) -> Vec<Section> {
    sections_with_prefix(markdown, spec_prefix(markdown))
}

fn sections_with_prefix(markdown: &str, prefix: &str) -> Vec<Section> {
    let mut sections = Vec::new();
    let mut fenced = false;

    for line in markdown.lines() {
        if line.trim_start().starts_with("```") {
            fenced = !fenced;
            continue;
        }
        if fenced {
            continue;
        }
        let Some(heading) = line.strip_prefix('#') else {
            continue;
        };
        let heading = heading.trim_start_matches('#');
        if !heading.starts_with(' ') {
            continue;
        }
        if let Some(section) = Section::with_prefix(prefix, heading) {
            sections.push(section);
        }
    }

    sections
}

fn spec_prefix(markdown: &str) -> &str {
    markdown
        .lines()
        .find(|line| line.trim().starts_with("<!-- normative: STD"))
        .map_or("LR", |_| "STD")
}

/// The numbered headings selected by the spec's `normative` directive.
pub fn normative_sections(markdown: &str) -> io::Result<Vec<Section>> {
    let mut directive = None;

    for line in markdown.lines() {
        let line = line.trim();
        let Some(value) = line
            .strip_prefix("<!-- normative:")
            .and_then(|line| line.strip_suffix("-->"))
        else {
            continue;
        };

        if directive.replace(value.trim()).is_some() {
            return Err(invalid("the spec has more than one normative directive"));
        }
    }

    let directive = directive.ok_or_else(|| invalid("the spec has no normative directive"))?;
    let selectors = directive
        .split(',')
        .map(str::trim)
        .map(selector)
        .collect::<io::Result<Vec<_>>>()?;
    let prefix = selectors
        .first()
        .map_or("LR", |selector| selector.first.prefix.as_str());
    if selectors
        .iter()
        .any(|selector| selector.first.prefix != prefix || selector.last.prefix != prefix)
    {
        return Err(invalid("a spec cannot mix section namespaces"));
    }
    let defined = sections_with_prefix(markdown, prefix);

    for selected in &selectors {
        if !defined.iter().any(|section| selected.contains(section)) {
            return Err(invalid("a normative selector names no spec section"));
        }
    }

    Ok(defined
        .into_iter()
        .filter(|section| selectors.iter().any(|selected| selected.contains(section)))
        .collect())
}

#[derive(Debug, Clone)]
struct Selector {
    first: Section,
    last: Section,
}

impl Selector {
    fn contains(&self, section: &Section) -> bool {
        &self.first <= section && section <= &self.last
    }
}

fn selector(text: &str) -> io::Result<Selector> {
    let (first, last) = match text.split_once('-') {
        Some((first, last)) => (first, last),
        None => (text, text),
    };
    let first = directive_section(first)?;
    let last = directive_section(last)?;

    if first > last {
        return Err(invalid("a normative section range runs backwards"));
    }

    Ok(Selector { first, last })
}

fn directive_section(text: &str) -> io::Result<Section> {
    let text = text.trim();
    let section = Section::parse(text).ok_or_else(|| invalid("invalid normative section"))?;
    if section.to_string() != text {
        return Err(invalid("invalid normative section"));
    }
    Ok(section)
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

/// What the suite covers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Coverage {
    /// Spec sections with at least one test, directly or through a subsection.
    pub tested: Vec<Section>,
    /// Spec sections with no test.
    pub untested: Vec<Section>,
    /// Sections tests cite that the spec does not define, and who cites them.
    /// Usually a typo, always a test that enforces nothing.
    pub unknown: BTreeMap<Section, Vec<String>>,
}

impl Coverage {
    #[must_use]
    pub fn section_count(&self) -> usize {
        self.tested.len() + self.untested.len()
    }
}

impl fmt::Display for Coverage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "spec coverage: {} of {} sections have tests",
            self.tested.len(),
            self.section_count()
        )?;

        if !self.untested.is_empty() {
            writeln!(f, "\nuntested sections:")?;
            for section in &self.untested {
                writeln!(f, "  {section}")?;
            }
        }

        if !self.unknown.is_empty() {
            writeln!(f, "\ncited but not in the spec:")?;
            for (section, citers) in &self.unknown {
                writeln!(f, "  {section} cited by {}", citers.join(", "))?;
            }
        }

        Ok(())
    }
}

/// Compares the sections a spec defines against the sections tests cite.
#[must_use]
pub fn coverage(spec: &[Section], citations: &BTreeMap<Section, Vec<String>>) -> Coverage {
    let defined: BTreeSet<&Section> = spec.iter().collect();

    let mut cited: BTreeSet<Section> = BTreeSet::new();
    let mut unknown = BTreeMap::new();
    for (section, citers) in citations {
        if defined.contains(section) {
            cited.insert(section.clone());
        } else {
            unknown.insert(section.clone(), citers.clone());
        }
    }

    let has_children: BTreeSet<Section> = spec.iter().flat_map(Section::ancestors).collect();

    let (tested, untested) = spec.iter().cloned().partition(|section| {
        cited.contains(section) || covered_by_children(section, spec, &cited, &has_children)
    });

    Coverage {
        tested,
        untested,
        unknown,
    }
}

/// A heading whose content is its subsections is covered once they all are.
fn covered_by_children(
    section: &Section,
    spec: &[Section],
    cited: &BTreeSet<Section>,
    has_children: &BTreeSet<Section>,
) -> bool {
    if !has_children.contains(section) {
        return false;
    }
    let prefix = format!("{}.", section.number);
    spec.iter()
        .filter(|other| other.prefix == section.prefix && other.number.starts_with(&prefix))
        .all(|child| cited.contains(child))
}

/// The sections cited by every test under `root`, and which files cite them.
pub fn citations(root: &Path) -> io::Result<BTreeMap<Section, Vec<String>>> {
    let mut citations: BTreeMap<Section, Vec<String>> = BTreeMap::new();

    for path in discover(root)? {
        let Ok(source) = fs::read_to_string(&path) else {
            continue;
        };
        let Ok(directives) = directives::parse(&source) else {
            continue;
        };

        let name = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .display()
            .to_string();

        for cited in &directives.spec {
            if let Some(section) = Section::parse(cited) {
                citations.entry(section).or_default().push(name.clone());
            }
        }
    }

    Ok(citations)
}

/// Reports coverage of the spec at `spec_path` by the suite at `suite_root`.
pub fn report(spec_path: &Path, suite_root: &Path) -> io::Result<Coverage> {
    let spec = fs::read_to_string(spec_path)?;
    Ok(coverage(
        &normative_sections(&spec)?,
        &citations(suite_root)?,
    ))
}
