use common::stdlib::HasBuiltinEmbed;
use fe_hir::{analysis::embed_requirements::check_embed_operator_annotations, hir_def::HirIngot};

use fe_hir::test_db::HirAnalysisTestDb;

#[test]
fn builtin_embed_has_operator_bindings() {
    let db = HirAnalysisTestDb::default();
    let embed = db.builtin_embed();
    let errors = check_embed_operator_annotations(&db, embed.root_mod(&db));
    assert!(errors.is_empty(), "{errors:#?}");
}
