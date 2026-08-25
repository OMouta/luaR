//! Which spec sections have tests, and which do not.
//!
//! The suite is only as good as its coverage of the specification, and the
//! honest way to know is to compare the sections the spec defines against the
//! sections tests cite. Both sides are read from files: the spec is not
//! compiled in, and its path is supplied by whoever runs the report.
//!
//! A section with subsections is covered when all of them are, since there is
//! nothing left to test in a heading whose content is its children.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;

use crate::{directives, discover};

/// A section number such as `11.1`, without the `§`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Section(String);

impl Section {
    /// Reads a section number from a heading or a citation, accepting `§11.1`,
    /// `11.1` and `11.` alike. `None` if there is no number to read.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        let text = text.trim().trim_start_matches('§').trim();
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
        Some(Self(number.to_owned()))
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// The sections this one sits inside: `11.1.2` yields `11.1` and `11`.
    fn ancestors(&self) -> impl Iterator<Item = Self> + '_ {
        self.0
            .match_indices('.')
            .map(|(i, _)| Self(self.0[..i].to_owned()))
    }

    /// Orders `11.2` before `11.10`, which string order gets wrong.
    fn key(&self) -> Vec<u32> {
        self.0.split('.').map(|p| p.parse().unwrap_or(0)).collect()
    }
}

impl fmt::Display for Section {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "§{}", self.0)
    }
}

impl PartialOrd for Section {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Section {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}

/// Every numbered heading in a Markdown specification, in document order.
///
/// Headings inside fenced code blocks are not sections.
#[must_use]
pub fn sections(markdown: &str) -> Vec<Section> {
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
        if let Some(section) = Section::parse(heading) {
            sections.push(section);
        }
    }

    sections
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
    let prefix = format!("{}.", section.0);
    spec.iter()
        .filter(|other| other.0.starts_with(&prefix))
        .all(|child| cited.contains(child))
}

/// The sections cited by every test under `root`, and which files cite them.
///
/// Files with an unreadable header are left out: the suite already fails on
/// them, and reporting them twice would not add anything.
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
    Ok(coverage(&sections(&spec), &citations(suite_root)?))
}
