use common::{impl_db_traits, InputDb};

use hir::{HirDb, LowerHirDb, SpannedHirDb};
use hir_analysis::{diagnostics::SpannedHirAnalysisDb, HirAnalysisDb};
// xxx use salsa::{ParallelDatabase, Snapshot};

#[salsa::db]
pub trait LanguageServerDb:
    salsa::Database + SpannedHirAnalysisDb + HirAnalysisDb + HirDb + LowerHirDb + SpannedHirDb + InputDb
{
}

#[salsa::db]
impl<DB> LanguageServerDb for DB where
    DB: Sized
        + salsa::Database
        + SpannedHirAnalysisDb
        + HirAnalysisDb
        + HirDb
        + LowerHirDb
        + SpannedHirDb
        + InputDb
{
}

#[salsa::db]
#[derive(Default, Clone)]
pub struct LanguageServerDatabase {
    storage: salsa::Storage<Self>,
}

impl_db_traits!(
    LanguageServerDatabase,
    InputDb,
    HirDb,
    LowerHirDb,
    SpannedHirDb,
    HirAnalysisDb,
    SpannedHirAnalysisDb,
);
