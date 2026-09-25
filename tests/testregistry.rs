use std::collections::BTreeSet;

use ghidra_decompiler::marshal::{ATTRIB_UNKNOWN, AttributeId, ELEM_UNKNOWN, ElementId};
use ghidra_decompiler::marshal_registry::{ATTRIBUTE_IDS, ELEMENT_IDS};

#[test]
fn attribute_registry_is_consistent() {
    let mut name_set = BTreeSet::new();
    let mut ids = BTreeSet::new();
    for attrib in ATTRIBUTE_IDS {
        assert!(
            name_set.insert(attrib.get_name()),
            "duplicate attribute name {}",
            attrib.get_name()
        );
        assert!(
            ids.insert(attrib.get_id()),
            "duplicate attribute id {}",
            attrib.get_id()
        );
        assert_eq!(AttributeId::find(attrib.get_name(), 0), attrib.get_id());
        assert_eq!(AttributeId::find(attrib.get_name(), 1), ATTRIB_UNKNOWN.get_id());
    }
    assert_eq!(AttributeId::find("not_an_attribute", 0), ATTRIB_UNKNOWN.get_id());
}

#[test]
fn element_registry_is_consistent() {
    let mut name_set = BTreeSet::new();
    let mut ids = BTreeSet::new();
    for elem in ELEMENT_IDS {
        assert!(
            name_set.insert(elem.get_name()),
            "duplicate element name {}",
            elem.get_name()
        );
        assert!(ids.insert(elem.get_id()), "duplicate element id {}", elem.get_id());
        assert_eq!(ElementId::find(elem.get_name(), 0), elem.get_id());
    }
    assert_eq!(ElementId::find("not_an_element", 0), ELEM_UNKNOWN.get_id());
}
