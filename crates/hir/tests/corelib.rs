use std::{fs, path::Path};

use common::InputDb;
use common::stdlib::{HasBuiltinCore, HasBuiltinStd};
use driver::{DriverDataBase, db::DiagnosticsCollection, init_ingot};
use tempfile::TempDir;
use url::Url;

#[cfg(target_arch = "wasm32")]
use test_utils::url_utils::UrlExt;

#[test]
fn analyze_corelib() {
    let db = DriverDataBase::default();
    let core = db.builtin_core();

    let core_diags = db.run_on_ingot(core);
    assert_builtin_clean(&db, core_diags, "core");
}

#[test]
fn analyze_stdlib() {
    let db = DriverDataBase::default();
    let std_ingot = db.builtin_std();

    let std_diags = db.run_on_ingot(std_ingot);
    assert_builtin_clean(&db, std_diags, "std");
}

fn assert_builtin_clean(db: &DriverDataBase, diags: DiagnosticsCollection<'_>, name: &str) {
    if diags.is_empty() {
        return;
    }

    diags.emit(db);
    panic!(
        "expected no diagnostics for builtin {name}, but got:\n{}",
        diags.format_diags(db)
    );
}

#[test]
fn analyze_custom_core_missing_effect_ref_does_not_panic_and_reports_requirement_diag() {
    let temp = TempDir::new().unwrap();
    write_file(
        &temp.path().join("fe.toml"),
        "[ingot]\nname = \"core\"\nversion = \"0.1.0\"\n",
    );
    write_file(
        &temp.path().join("src/lib.fe"),
        r#"
pub struct Ctx {}

fn exercise() uses (ctx: Ctx) {}
"#,
    );
    write_file(
        &temp.path().join("src/effect_ref.fe"),
        r#"
pub trait EffectRefMut<T>: EffectRef<T> {}
pub trait EffectHandle {
    type Target
}
"#,
    );

    let diags = analyze_ingot_diags(temp.path());
    assert!(
        diags.contains("missing required core trait `core::effect_ref::EffectRef`"),
        "expected missing EffectRef diagnostic, got:\n{diags}",
    );
}

fn analyze_ingot_diags(root: &Path) -> String {
    let mut db = DriverDataBase::default();
    let root_url = Url::from_directory_path(root).expect("root url");
    let _ = init_ingot(&mut db, &root_url);
    let ingot = db
        .workspace()
        .containing_ingot(&db, root_url)
        .expect("ingot should load");
    db.run_on_ingot(ingot).format_diags(&db)
}

fn write_file(path: &Path, content: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(path, content).unwrap();
}
