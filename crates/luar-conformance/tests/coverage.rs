//! Tests the spec coverage report.

use std::collections::BTreeMap;

use luar_conformance::coverage::{Section, coverage, sections};

const SPEC: &str = "\
# A Specification

## 4. Literals

### 4.3 Integers

## 11. Operators

### 11.1 Arithmetic

### 11.2 Concatenation

```lua
## 99. Not a section, it is inside a code fence
```

## 80. Diagnostics
";

fn cite(sections: &[&str]) -> BTreeMap<Section, Vec<String>> {
    sections
        .iter()
        .map(|s| {
            (
                Section::parse(s).expect("a section number"),
                vec!["a-test.luar".to_owned()],
            )
        })
        .collect()
}

#[test]
fn headings_become_sections_and_code_fences_do_not() {
    let found: Vec<String> = sections(SPEC).iter().map(Section::to_string).collect();
    assert_eq!(found, ["§4", "§4.3", "§11", "§11.1", "§11.2", "§80"]);
}

#[test]
fn untested_sections_are_listed_in_spec_order() {
    let report = coverage(&sections(SPEC), &cite(&["§11.1"]));
    let untested: Vec<String> = report.untested.iter().map(Section::to_string).collect();

    assert_eq!(untested, ["§4", "§4.3", "§11", "§11.2", "§80"]);
    assert_eq!(report.tested.len(), 1);
    assert_eq!(report.section_count(), 6);
}

#[test]
fn a_heading_is_covered_once_all_its_subsections_are() {
    let report = coverage(&sections(SPEC), &cite(&["§11.1", "§11.2"]));
    let tested: Vec<String> = report.tested.iter().map(Section::to_string).collect();

    // §11 has nothing to test beyond its subsections. §4 still does, since
    // §4.3 is untested.
    assert_eq!(tested, ["§11", "§11.1", "§11.2"]);
}

#[test]
fn citing_a_section_the_spec_does_not_have_is_reported() {
    let report = coverage(&sections(SPEC), &cite(&["§11.1", "§93.4"]));

    let unknown: Vec<String> = report.unknown.keys().map(Section::to_string).collect();
    assert_eq!(unknown, ["§93.4"]);
    assert_eq!(
        report.unknown[&Section::parse("§93.4").unwrap()],
        ["a-test.luar"]
    );
}

#[test]
fn sections_sort_by_number_not_by_text() {
    let mut found = [
        Section::parse("§11.10").unwrap(),
        Section::parse("§11.2").unwrap(),
        Section::parse("§9").unwrap(),
    ];
    found.sort();

    let sorted: Vec<String> = found.iter().map(Section::to_string).collect();
    assert_eq!(sorted, ["§9", "§11.2", "§11.10"]);
}

#[test]
fn a_citation_without_a_number_is_not_a_section() {
    assert!(Section::parse("§").is_none());
    assert!(Section::parse("arithmetic").is_none());
    assert_eq!(Section::parse("11. Operators").unwrap().as_str(), "11");
}
