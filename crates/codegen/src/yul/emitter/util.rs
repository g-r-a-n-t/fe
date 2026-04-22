pub(super) use crate::yul::names::{prefix_yul_name, sanitize_yul_ident};

pub(super) fn section_object_label(name: &mir::RuntimeSectionName) -> String {
    match name {
        mir::RuntimeSectionName::Init => "init".to_string(),
        mir::RuntimeSectionName::Runtime => "runtime".to_string(),
        mir::RuntimeSectionName::Main => "main".to_string(),
        mir::RuntimeSectionName::Test(name) => sanitize_yul_ident(name),
        mir::RuntimeSectionName::CodeRegion(symbol) => sanitize_yul_ident(symbol),
    }
}
