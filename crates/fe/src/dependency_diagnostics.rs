use std::{collections::HashSet, fmt::Write as _};

use common::{InputDb, diagnostics::CompleteDiagnostic, file::IngotFileKind};
use driver::{DriverDataBase, db::DiagnosticsCollection};
use url::Url;

pub(crate) struct DependencyIssues<'db> {
    issues: Vec<DependencyIssue<'db>>,
}

enum DependencyIssue<'db> {
    MissingSourceFiles(Url),
    Diagnostics {
        url: Url,
        hir: DiagnosticsCollection<'db>,
        mir: Vec<CompleteDiagnostic>,
    },
}

impl DependencyIssue<'_> {
    fn format(&self, db: &DriverDataBase, out: &mut String) {
        let url = match self {
            Self::MissingSourceFiles(url) | Self::Diagnostics { url, .. } => url,
        };
        append_dependency_header(db, url, out);
        match self {
            DependencyIssue::MissingSourceFiles(url) => {
                let _ = writeln!(out, "Error: Could not find source files for ingot {url}");
            }
            DependencyIssue::Diagnostics { hir, mir, .. } => {
                if !hir.is_empty() {
                    out.push_str(&hir.format_diags(db));
                }
                if !mir.is_empty() {
                    out.push_str(&db.format_complete_diagnostics(mir));
                }
            }
        }
        if !out.ends_with('\n') {
            out.push('\n');
        }
    }
}

impl<'db> DependencyIssues<'db> {
    pub(crate) fn collect(
        db: &'db DriverDataBase,
        ingot_url: &Url,
        seen: &mut HashSet<Url>,
    ) -> Self {
        let mut issues = Vec::new();
        for dependency_url in db.dependency_graph().dependency_urls(db, ingot_url) {
            if !seen.insert(dependency_url.clone()) {
                continue;
            }
            let Some(ingot) = db.workspace().containing_ingot(db, dependency_url.clone()) else {
                continue;
            };
            if !ingot_has_source_files(db, ingot) {
                issues.push(DependencyIssue::MissingSourceFiles(dependency_url));
                continue;
            }
            let hir = db.run_on_ingot(ingot);
            let mir = if hir.has_errors(db) {
                Vec::new()
            } else {
                db.mir_diagnostics_for_ingot(ingot)
            };
            if !hir.is_empty() || !mir.is_empty() {
                issues.push(DependencyIssue::Diagnostics {
                    url: dependency_url,
                    hir,
                    mir,
                });
            }
        }
        Self { issues }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.issues.is_empty()
    }

    pub(crate) fn message(&self) -> &'static str {
        if self.issues.len() == 1 {
            "Errors in dependency"
        } else {
            "Errors in dependencies"
        }
    }

    pub(crate) fn format(&self, db: &DriverDataBase) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "Error: {}", self.message());
        for issue in &self.issues {
            issue.format(db, &mut out);
            out.push('\n');
        }
        out
    }
}

fn ingot_has_source_files(db: &DriverDataBase, ingot: hir::Ingot<'_>) -> bool {
    ingot
        .files(db)
        .iter()
        .any(|(_, file)| matches!(file.kind(db), Some(IngotFileKind::Source)))
}

fn append_dependency_header(db: &DriverDataBase, dependency_url: &Url, out: &mut String) {
    let dependency = if let Some(ingot) =
        db.workspace().containing_ingot(db, dependency_url.clone())
        && let Some(config) = ingot.config(db)
    {
        let name = config.metadata.name.as_deref().unwrap_or("unknown");
        if let Some(version) = &config.metadata.version {
            format!("Dependency: {name} (version: {version})")
        } else {
            format!("Dependency: {name}")
        }
    } else {
        "Dependency: <unknown>".to_string()
    };
    let _ = writeln!(out, "\n{dependency}\nURL: {dependency_url}\n");
}
