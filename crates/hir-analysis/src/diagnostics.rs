//! This module defines the diagnostics that can be accumulated inside salsa-db
//! with span-agnostic forms. All diagnostics accumulated in salsa-db should
//! implement [`DiagnosticVoucher`] which defines the conversion into
//! [`CompleteDiagnostic`].

use crate::{
    name_resolution::diagnostics::NameResDiag,
    ty::{
        diagnostics::{
            BodyDiag, DefConflictError, FuncBodyDiag, ImplDiag, TraitConstraintDiag,
            TraitLowerDiag, TyDiagCollection, TyLowerDiag,
        },
        trait_def::TraitDef,
        ty_check::RecordLike,
        ty_def::{TyData, TyVarSort},
    },
    HirAnalysisDb,
};
use common::diagnostics::{
    CompleteDiagnostic, DiagnosticPass, GlobalErrorCode, LabelStyle, Severity, Span, SpanKind,
    SubDiagnostic,
};
use either::Either;
use hir::{hir_def::FieldIndex, span::LazySpan, ParserError, SpannedHirDb};
use itertools::Itertools;

/// All diagnostics accumulated in salsa-db should implement
/// [`DiagnosticVoucher`] which defines the conversion into
/// [`CompleteDiagnostic`].
///
/// All types that implement `DiagnosticVoucher` must NOT have a span
/// information which invalidates cache in salsa-db. Instead of it, the all
/// information is given by [`SpannedHirDb`] to allow evaluating span lazily.
///
/// The reason why we use `DiagnosticVoucher` is that we want to evaluate span
/// lazily to avoid invalidating cache in salsa-db.
///
/// To obtain a span from HIR nodes in a lazy manner, it's recommended to use
/// `[LazySpan]`(crate::span::LazySpan) and types that implement `LazySpan`.
pub trait DiagnosticVoucher: Send + Sync {
    /// Makes a [`CompleteDiagnostic`].
    fn to_complete(&self, db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic;
}

impl DiagnosticVoucher for CompleteDiagnostic {
    fn to_complete(&self, _db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic {
        self.clone()
    }
}

#[salsa::db]
pub trait SpannedHirAnalysisDb:
    salsa::Database + hir::HirDb + hir::SpannedHirDb + HirAnalysisDb
{
}

#[salsa::db]
impl<T> SpannedHirAnalysisDb for T where T: HirAnalysisDb + SpannedHirDb {}

// `ParseError` has span information, but this is not a problem because the
// parsing procedure itself depends on the file content, and thus span
// information.
impl DiagnosticVoucher for ParserError {
    fn to_complete(&self, _db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic {
        let error_code = GlobalErrorCode::new(DiagnosticPass::Parse, 1);
        let span = Span::new(self.file, self.error.range(), SpanKind::Original);
        CompleteDiagnostic::new(
            Severity::Error,
            self.error.msg(),
            vec![SubDiagnostic::new(
                LabelStyle::Primary,
                self.error.label(),
                Some(span),
            )],
            vec![],
            error_code,
        )
    }
}

pub trait LazyDiagnostic<'db> {
    fn to_complete(&self, db: &'db dyn SpannedHirAnalysisDb) -> CompleteDiagnostic;
}

impl DiagnosticVoucher for DefConflictError<'_> {
    fn to_complete(&self, db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic {
        let mut items = self.0.iter();
        let first = items.next().unwrap();
        let name = first.name(db).unwrap().data(db);
        CompleteDiagnostic {
            severity: Severity::Error,
            message: format!("conflicting definitions of `{name}`",),
            sub_diagnostics: {
                let mut subs = vec![SubDiagnostic::new(
                    LabelStyle::Primary,
                    format!("`{name}` is defined here"),
                    first.name_span().unwrap().resolve(db),
                )];
                subs.extend(items.map(|item| {
                    SubDiagnostic::new(
                        LabelStyle::Secondary,
                        format! {"`{name}` is redefined here"},
                        item.name_span().unwrap().resolve(db),
                    )
                }));
                subs
            },
            notes: vec![],
            error_code: GlobalErrorCode::new(DiagnosticPass::TypeDefinition, 100),
        }
    }
}

impl DiagnosticVoucher for FuncBodyDiag<'_> {
    fn to_complete(&self, db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic {
        match self {
            Self::Ty(diag) => diag.to_complete(db),
            Self::Body(diag) => diag.to_complete(db),
            Self::NameRes(diag) => diag.to_complete(db),
        }
    }
}

impl DiagnosticVoucher for TyDiagCollection<'_> {
    fn to_complete(&self, db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic {
        match self {
            Self::Ty(diag) => diag.to_complete(db),
            Self::PathRes(diag) => diag.to_complete(db),
            Self::Satisfiability(diag) => diag.to_complete(db),
            Self::TraitLower(diag) => diag.to_complete(db),
            Self::Impl(diag) => diag.to_complete(db),
        }
    }
}

impl DiagnosticVoucher for NameResDiag<'_> {
    fn to_complete(&self, db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic {
        let error_code = GlobalErrorCode::new(DiagnosticPass::NameResolution, self.local_code());
        let severity = Severity::Error;
        match self {
            Self::Conflict(ident, conflicts) => {
                let ident = ident.data(db);
                let mut spans: Vec<_> = conflicts
                    .iter()
                    .filter_map(|span| span.resolve(db))
                    .collect();
                spans.sort_unstable();
                let mut spans = spans.into_iter();
                let mut diags = Vec::with_capacity(conflicts.len());
                diags.push(SubDiagnostic::new(
                    LabelStyle::Primary,
                    format!("`{ident}` is defined here"),
                    spans.next(),
                ));
                for sub_span in spans {
                    diags.push(SubDiagnostic::new(
                        LabelStyle::Secondary,
                        format! {"`{ident}` is redefined here"},
                        Some(sub_span),
                    ));
                }

                CompleteDiagnostic {
                    severity,
                    message: format!("`{ident}` conflicts with other definitions"),
                    sub_diagnostics: diags,
                    notes: vec![],
                    error_code,
                }
            }

            Self::NotFound(prim_span, ident) => {
                let ident = ident.data(db);
                CompleteDiagnostic {
                    severity,
                    message: format!("`{ident}` is not found"),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("`{ident}` is not found"),
                        span: prim_span.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::Invisible(prim_span, ident, span) => {
                let ident = ident.data(db);

                let mut sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("`{ident}` is not visible"),
                    span: prim_span.resolve(db),
                }];
                if let Some(span) = span {
                    sub_diagnostics.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("`{ident}` is defined here"),
                        span: span.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity,
                    message: format!("`{ident}` is not visible"),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }

            Self::Ambiguous(prim_span, ident, candidates) => {
                let ident = ident.data(db);
                let mut diags = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("`{ident}` is ambiguous"),
                    span: prim_span.resolve(db),
                }];

                let mut cand_spans: Vec<_> = candidates
                    .iter()
                    .filter_map(|span| span.resolve(db))
                    .collect();
                cand_spans.sort_unstable();
                diags.extend(cand_spans.into_iter().enumerate().map(|(i, span)| {
                    SubDiagnostic::new(
                        LabelStyle::Secondary,
                        format!("candidate {}", i + 1),
                        Some(span),
                    )
                }));

                CompleteDiagnostic {
                    severity,
                    message: format!("`{ident}` is ambiguous"),
                    sub_diagnostics: diags,
                    notes: vec![],
                    error_code,
                }
            }

            Self::InvalidPathSegment(prim_span, name, res_span) => {
                let name = name.data(db);
                let mut labels = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("`{name}` can't be used as a middle segment of a path"),
                    span: prim_span.resolve(db),
                }];

                if let Some(span) = res_span {
                    labels.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("`{name}` is defined here"),
                        span: span.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity,
                    message: format!("`{name}` can't be used as a middle segment of a path"),
                    sub_diagnostics: labels,
                    notes: vec![],
                    error_code,
                }
            }

            Self::ExpectedType(prim_span, name, given_kind) => {
                let name = name.data(db);
                CompleteDiagnostic {
                    severity,
                    message: "expected type item here".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("expected type here, but found {given_kind} `{name}`"),
                        span: prim_span.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::ExpectedTrait(prim_span, name, given_kind) => {
                let name = name.data(db);
                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "expected trait item here".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("expected trait here, but found {given_kind} `{name}`"),
                        span: prim_span.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::ExpectedValue(prim_span, name, given_kind) => {
                let name = name.data(db);
                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "expected value here".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("expected value here, but found {given_kind} `{name}`"),
                        span: prim_span.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::TooManyGenericArgs {
                span,
                expected,
                given,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: format!("too many generic args; expected {expected}, given {given}"),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("expected {expected} arguments here, but {given} given"),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },
        }
    }
}

impl DiagnosticVoucher for TyLowerDiag<'_> {
    fn to_complete(&self, db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic {
        let error_code = GlobalErrorCode::new(DiagnosticPass::TypeDefinition, self.local_code());
        match self {
            Self::ExpectedStarKind(span) => {
                // find expected ty name, num of generic args, etc
                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "expected `*` kind in this context".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: "expected `*` kind here".to_string(),
                        span: span.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::InvalidTypeArgKind {
                span,
                given,
                expected,
            } => {
                let msg = if let Some(expected) = expected {
                    let arg_kind = given.kind(db);
                    debug_assert!(!expected.does_match(arg_kind));

                    format!(
                        "expected `{}` kind, but `{}` has `{}` kind",
                        expected,
                        given.pretty_print(db),
                        arg_kind
                    )
                } else {
                    "too many generic arguments".to_string()
                };

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "invalid type argument kind".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: msg.to_string(),
                        span: span.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::TooManyGenericArgs {
                span,
                expected,
                given,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: format!("too many generic args; expected {expected}, given {given}"),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("expected {expected} arguments, but {given} were given"),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            // TODO: add hint about indirection (eg *T)
            Self::RecursiveType(cycle) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "recursive type definition".to_string(),
                sub_diagnostics: {
                    let head = cycle.first().unwrap();
                    let mut subs = vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: "recursive type definition here".to_string(),
                        span: head.adt.adt_ref(db).name_span(db).resolve(db),
                    }];
                    subs.extend(cycle.iter().map(|m| {
                        SubDiagnostic {
                            style: LabelStyle::Secondary,
                            message: "recursion occurs here".to_string(),
                            span: m
                                .adt
                                .variant_ty_span(db, m.field_idx as usize, m.ty_idx as usize)
                                .resolve(db),
                        }
                    }));
                    subs
                },
                notes: vec![],
                error_code,
            },
            Self::UnboundTypeAliasParam {
                span,
                alias,
                n_given_args: _,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "all type parameters of type alias must be given".to_string(),
                sub_diagnostics: vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!(
                            "expected at least {} arguments here",
                            alias.generic_params(db).len(db)
                        ),
                        span: span.resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: "type alias defined here".to_string(),
                        span: alias.span().resolve(db),
                    },
                ],
                notes: vec![],
                error_code,
            },

            Self::TypeAliasCycle { cycle } => {
                let mut cycle = cycle.clone();
                cycle.sort_by_key(|a| a.span().resolve(db));

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "type alias cycle".to_string(),
                    sub_diagnostics: {
                        let mut iter = cycle.iter();
                        let mut labels = vec![SubDiagnostic {
                            style: LabelStyle::Primary,
                            message: "cycle happens here".to_string(),
                            span: iter.next_back().unwrap().span().ty().resolve(db),
                        }];
                        labels.extend(iter.map(|type_alias| SubDiagnostic {
                            style: LabelStyle::Secondary,
                            message: "type alias defined here".to_string(),
                            span: type_alias.span().alias().resolve(db),
                        }));
                        labels
                    },
                    notes: vec![],
                    error_code,
                }
            }

            Self::InconsistentKindBound { span, ty, bound } => {
                let msg = format!(
                    "`{}` is already declared with `{}` kind, but found `{}` kind here",
                    ty.pretty_print(db),
                    ty.kind(db),
                    bound
                );

                CompleteDiagnostic {
                    severity: Severity::Error,
                    // TODO improve message
                    message: "duplicate type bound is not allowed.".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: msg.to_string(),
                        span: span.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::KindBoundNotAllowed(span) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "kind bound is not allowed".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "kind bound is not allowed here".to_string(),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::GenericParamAlreadyDefinedInParent {
                span,
                conflict_with,
                name,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "generic parameter is already defined in the parent item".to_string(),
                sub_diagnostics: vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("`{}` is already defined", name.data(db)),
                        span: span.resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: "conflict with this generic parameter".to_string(),
                        span: conflict_with.resolve(db),
                    },
                ],
                notes: vec![],
                error_code,
            },

            Self::DuplicateArgName(func, idxs) => {
                let name = func.params(db).unwrap().data(db)[idxs[0] as usize]
                    .name()
                    .unwrap()
                    .data(db);

                let pspan = func.span().params();
                let spans = idxs
                    .iter()
                    .map(|i| pspan.clone().param(*i as usize).name().resolve(db));

                let message = if let Some(name) = func.name(db).to_opt() {
                    format!("duplicate argument name in function `{}`", name.data(db))
                } else {
                    "duplicate argument name in function definition".into()
                };

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message,
                    sub_diagnostics: duplicate_name_subdiags(name, spans),
                    notes: vec![],
                    error_code,
                }
            }

            Self::DuplicateArgLabel(func, idxs) => {
                let params = func.params(db).unwrap().data(db);
                let name = params[idxs[0] as usize].label_eagerly().unwrap().data(db);

                let spans = idxs.iter().map(|i| {
                    let s = func.span().params().clone().param(*i as usize);
                    if params[*i as usize].label.is_some() {
                        s.label().resolve(db)
                    } else {
                        s.name().resolve(db)
                    }
                });

                let message = if let Some(name) = func.name(db).to_opt() {
                    format!("duplicate argument label in function `{}`", name.data(db))
                } else {
                    "duplicate argument label in function definition".into()
                };

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message,
                    sub_diagnostics: duplicate_name_subdiags(name, spans),
                    notes: vec![],
                    error_code,
                }
            }

            Self::DuplicateFieldName(parent, idxs) => {
                let name = parent.fields(db).data(db)[idxs[0] as usize]
                    .name
                    .unwrap()
                    .data(db);

                let spans = idxs
                    .iter()
                    .map(|i| parent.field_name_span(*i as usize).resolve(db));

                let kind = parent.kind_name();
                let message = if let Some(name) = parent.name(db) {
                    format!("duplicate field name in {kind} `{name}`")
                } else {
                    format!("duplicate field name in {kind} definition")
                };

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message,
                    sub_diagnostics: duplicate_name_subdiags(name, spans),
                    notes: vec![],
                    error_code,
                }
            }

            Self::DuplicateVariantName(enum_, idxs) => {
                let message = if let Some(name) = enum_.name(db).to_opt() {
                    format!("duplicate variant name in enum `{}`", name.data(db))
                } else {
                    "duplicate variant name in enum definition".into()
                };

                let name = enum_.variants(db).data(db)[idxs[0] as usize]
                    .name
                    .unwrap()
                    .data(db);
                let spans = idxs
                    .iter()
                    .map(|i| enum_.span().variants().variant(*i as usize).resolve(db));
                CompleteDiagnostic {
                    severity: Severity::Error,
                    message,
                    sub_diagnostics: duplicate_name_subdiags(name, spans),
                    notes: vec![],
                    error_code,
                }
            }

            Self::DuplicateGenericParamName(adt, idxs) => {
                let message = if let Some(name) = adt.name(db) {
                    format!(
                        "duplicate generic parameter name in {} `{}`",
                        adt.kind_name(),
                        name.data(db)
                    )
                } else {
                    format!(
                        "duplicate generic parameter name in {} definition",
                        adt.kind_name()
                    )
                };

                let gen = adt.generic_owner().unwrap();
                let name = gen.params(db).data(db)[0].name().unwrap().data(db);
                let spans = idxs
                    .iter()
                    .map(|i| gen.params_span().param(*i as usize).resolve(db));
                CompleteDiagnostic {
                    severity: Severity::Error,
                    message,
                    sub_diagnostics: duplicate_name_subdiags(name, spans),
                    notes: vec![],
                    error_code,
                }
            }

            Self::InvalidConstParamTy(span) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "invalid const parameter type".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "only integer or bool types are allowed as a const parameter type"
                        .to_string(),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::RecursiveConstParamTy(span) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "recursive const parameter type is not allowed".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "recursive const parameter type is detected here".to_string(),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::ConstTyMismatch {
                span,
                expected,
                given,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "given type doesn't match the expected const type".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!(
                        "expected `{}` type here, but `{}` is given",
                        expected.pretty_print(db),
                        given.pretty_print(db)
                    ),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::ConstTyExpected { span, expected } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "expected const type".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!(
                        "expected const type of `{}` here",
                        expected.pretty_print(db)
                    ),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::NormalTypeExpected { span, given } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "expected a normal type".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!(
                        "expected a normal type here, but `{}` is given",
                        given.pretty_print(db)
                    ),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::AssocTy(span) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "associated type is not supported ".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "associated type is not implemented".to_string(),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::InvalidConstTyExpr(span) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "the expression is not supported yet in a const type context".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "only literal expression is supported".to_string(),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },
        }
    }
}

fn duplicate_name_subdiags<I>(name: &str, spans: I) -> Vec<SubDiagnostic>
where
    I: Iterator<Item = Option<Span>>,
{
    let mut spans = spans;
    let mut subs = vec![SubDiagnostic::new(
        LabelStyle::Primary,
        format!("`{name}` is defined here"),
        spans.next().unwrap(),
    )];
    subs.extend(spans.map(|span| {
        SubDiagnostic::new(
            LabelStyle::Secondary,
            format!("`{name}` is redefined here"),
            span,
        )
    }));
    subs
}

impl DiagnosticVoucher for BodyDiag<'_> {
    fn to_complete(&self, db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic {
        let error_code = GlobalErrorCode::new(DiagnosticPass::TyCheck, self.local_code());
        let severity = Severity::Error;

        match self {
            Self::TypeMismatch {
                span,
                expected,
                given,
            } => CompleteDiagnostic {
                severity,
                message: "type mismatch".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!(
                        "expected `{}`, but `{}` is given",
                        expected.pretty_print(db),
                        given.pretty_print(db),
                    ),
                    span: span.resolve(db),
                }],
                error_code,
                notes: vec![],
            },
            Self::InfiniteOccurrence(span) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "infinite sized type found".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "infinite sized type found".to_string(),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::DuplicatedBinding {
                primary,
                conflicat_with,
                name,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: format!("duplicate binding `{}` in pattern", name.data(db)),
                sub_diagnostics: vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("`{}` is defined again here", name.data(db)),
                        span: primary.resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("first definition of `{}` in this pattern", name.data(db)),
                        span: conflicat_with.resolve(db),
                    },
                ],
                notes: vec![],
                error_code,
            },

            Self::DuplicatedRestPat(span) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "duplicate `..` in pattern".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "`..` can be used only once".to_string(),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::InvalidPathDomainInPat { primary, resolved } => {
                let mut labels = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "expected type or enum variant here".to_string(),
                    span: primary.resolve(db),
                }];

                if let Some(resolved) = resolved {
                    labels.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: "this item given".to_string(),
                        span: resolved.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "invalid item is given here".to_string(),
                    sub_diagnostics: labels,
                    notes: vec![],
                    error_code,
                }
            }

            Self::UnitVariantExpected {
                primary,
                kind_name,
                hint,
            } => {
                let mut labels = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("expected unit variant here, but found {kind_name}"),
                    span: primary.resolve(db),
                }];

                if let Some(hint) = hint {
                    labels.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("Consider using `{hint}` instead"),
                        span: primary.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "expected unit variant".to_string(),
                    sub_diagnostics: labels,
                    notes: vec![],
                    error_code,
                }
            }

            Self::TupleVariantExpected {
                primary,
                kind_name,
                hint,
            } => {
                let mut labels = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: if let Some(kind_name) = kind_name {
                        format!("expected tuple variant here, but found {kind_name}")
                    } else {
                        "expected tuple variant here".to_string()
                    },
                    span: primary.resolve(db),
                }];

                if let Some(hint) = hint {
                    labels.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("Consider using `{hint}` instead"),
                        span: primary.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "expected tuple variant".to_string(),
                    sub_diagnostics: labels,
                    notes: vec![],
                    error_code,
                }
            }

            Self::RecordExpected {
                primary,
                kind_name,
                hint,
            } => {
                let mut labels = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: if let Some(kind_name) = kind_name {
                        format!("expected record variant or struct here, but found {kind_name}")
                    } else {
                        "expected record variant or struct here".to_string()
                    },
                    span: primary.resolve(db),
                }];

                if let Some(hint) = hint {
                    labels.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("Consider using `{hint}` instead"),
                        span: primary.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "expected record variant or struct".to_string(),
                    sub_diagnostics: labels,
                    notes: vec![],
                    error_code,
                }
            }

            Self::MismatchedFieldCount {
                primary,
                expected,
                given,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "field count mismatch".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("expected {expected} fields here, but {given} given"),
                    span: primary.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::DuplicatedRecordFieldBind {
                primary,
                first_use,
                name,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "duplicated record field binding".to_string(),
                sub_diagnostics: vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("duplicate field binding `{}`", name.data(db)),
                        span: primary.resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("first use of `{}`", name.data(db)),
                        span: first_use.resolve(db),
                    },
                ],
                notes: vec![],
                error_code,
            },

            Self::RecordFieldNotFound { span, label } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "specified field not found".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("field `{}` not found", label.data(db)),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::ExplicitLabelExpectedInRecord { primary, hint } => {
                let mut sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "explicit label is required".to_string(),
                    span: primary.resolve(db),
                }];

                if let Some(hint) = hint {
                    sub_diagnostics.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("Consider using `{hint}` instead"),
                        span: primary.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "explicit label is required".to_string(),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }

            Self::MissingRecordFields {
                primary,
                missing_fields,
                hint,
            } => {
                let missing = missing_fields
                    .iter()
                    .map(|id| id.data(db).as_str())
                    .collect::<Vec<_>>()
                    .join(", ");

                let mut sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("missing `{missing}`"),
                    span: primary.resolve(db),
                }];

                if let Some(hint) = hint {
                    sub_diagnostics.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("Consider using `{hint}` instead"),
                        span: primary.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "missing fields in record pattern".to_string(),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }

            Self::UndefinedVariable(primary, ident) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "undefined variable".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("undefined variable `{}`", ident.data(db)),
                    span: primary.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::ReturnedTypeMismatch {
                primary,
                actual,
                expected,
                func,
            } => {
                let actual = actual.pretty_print(db);
                let expected = expected.pretty_print(db);
                let mut sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("expected `{expected}`, but `{actual}` is returned"),
                    span: primary.resolve(db),
                }];

                if let Some(func) = func {
                    if func.ret_ty(db).is_some() {
                        sub_diagnostics.push(SubDiagnostic {
                            style: LabelStyle::Secondary,
                            message: format!("this function expects `{expected}` to be returned"),
                            span: func.span().ret_ty().resolve(db),
                        });
                    } else {
                        sub_diagnostics.push(SubDiagnostic {
                            style: LabelStyle::Secondary,
                            message: format!("try adding `-> {actual}`"),
                            span: func.span().name().resolve(db),
                        });
                    }
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "returned type mismatch".to_string(),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }
            Self::TypeMustBeKnown(span) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "type must be known here".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "type must be known here".to_string(),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::AccessedFieldNotFound {
                primary,
                given_ty,
                index,
            } => {
                let message = match index {
                    FieldIndex::Ident(ident) => format!(
                        "field `{}` is not found in `{}`",
                        ident.data(db),
                        given_ty.pretty_print(db)
                    ),
                    FieldIndex::Index(index) => format!(
                        "field `{}` is not found in `{}`",
                        index.data(db),
                        given_ty.pretty_print(db)
                    ),
                };

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "invalid field index".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message,
                        span: primary.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::OpsTraitNotImplemented {
                span,
                ty,
                op,
                trait_path,
            } => {
                let sub_diagnostics = vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("`{}` can't be applied to `{}`", op.data(db), ty),
                        span: span.resolve(db),
                    },
                    // TODO move to hint
                    SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!(
                            "Try implementing `{}` for `{}`",
                            trait_path.pretty_print(db),
                            ty
                        ),
                        span: span.resolve(db),
                    },
                ];

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: format!("`{}` trait is not implemented", trait_path.pretty_print(db)),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }

            Self::NonAssignableExpr(primary) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "not assignable left-hand side of assignment".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "cant assign to this expression".to_string(),
                    span: primary.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::ImmutableAssignment { primary, binding } => {
                let mut sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "immutable assignment".to_string(),
                    span: primary.resolve(db),
                }];

                if let Some((name, span)) = binding {
                    sub_diagnostics.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("try changing to `mut {}`", name.data(db)),
                        span: span.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "left-hand side of assignment is immutable".to_string(),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }

            Self::LoopControlOutsideOfLoop { primary, is_break } => {
                let stmt = if *is_break { "break" } else { "continue" };

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: format!("`{stmt}` is not allowed outside of a loop"),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("`{stmt}` is not allowed here"),
                        span: primary.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::TraitNotImplemented {
                primary,
                ty,
                trait_name,
            } => {
                let trait_name = trait_name.data(db);

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: format!("`{trait_name}` needs to be implemented for {ty}"),
                    sub_diagnostics: vec![
                        SubDiagnostic {
                            style: LabelStyle::Primary,
                            message: format!("`{trait_name}` needs to be implemented for `{ty}`"),
                            span: primary.resolve(db),
                        },
                        SubDiagnostic {
                            style: LabelStyle::Secondary,
                            message: format!("consider implementing `{trait_name}` for `{ty}`"),
                            span: primary.resolve(db),
                        },
                    ],
                    notes: vec![],
                    error_code,
                }
            }

            Self::NotCallable(primary, ty) => {
                let ty = ty.pretty_print(db);
                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: format!("expected function, found `{ty}`"),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!(
                            "call expression requires function; `{ty}` is not callable"
                        ),
                        span: primary.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::CallGenericArgNumMismatch {
                primary,
                def_span,
                given,
                expected,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "given generic argument number mismatch".to_string(),
                sub_diagnostics: vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!(
                            "expected {expected} generic arguments, but {given} given"
                        ),
                        span: primary.resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: "function defined here".to_string(),
                        span: def_span.resolve(db),
                    },
                ],
                notes: vec![],
                error_code,
            },

            Self::CallArgNumMismatch {
                primary,
                def_span,
                given,
                expected,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "argument number mismatch".to_string(),
                sub_diagnostics: vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("expected {expected} arguments, but {given} given"),
                        span: primary.resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: "function defined here".to_string(),
                        span: def_span.resolve(db),
                    },
                ],
                notes: vec![],
                error_code,
            },

            Self::CallArgLabelMismatch {
                primary,
                def_span,
                given,
                expected,
            } => {
                let mut sub_diagnostics = if let Some(given) = given {
                    vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!(
                            "expected `{}` label, but `{}` given",
                            expected.data(db),
                            given.data(db)
                        ),
                        span: primary.resolve(db),
                    }]
                } else {
                    vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("expected `{}` label", expected.data(db)),
                        span: primary.resolve(db),
                    }]
                };

                sub_diagnostics.push(SubDiagnostic {
                    style: LabelStyle::Secondary,
                    message: "function defined here".to_string(),
                    span: def_span.resolve(db),
                });

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "argument label mismatch".to_string(),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }

            Self::NotAMethod {
                span,
                receiver_ty,
                func_name,
                func_ty,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: format!("`{}` is not a method", func_name.data(db)),
                sub_diagnostics: vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!(
                            "`{}` is an associated function, not a method",
                            func_name.data(db),
                        ),
                        span: span.clone().method_name().resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!(
                            "help: use associated function syntax instead: `{}::{}`",
                            receiver_ty.pretty_print(db),
                            func_name.data(db)
                        ),
                        span: span.resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: "function defined here".to_string(),
                        span: func_ty.name_span(db).unwrap().resolve(db),
                    },
                ],
                notes: vec![
                    "note: to be used as a method, a function must have a `self` parameter"
                        .to_string(),
                ],
                error_code,
            },

            Self::AmbiguousInherentMethodCall {
                primary,
                method_name,
                cand_spans,
            } => {
                let method_name = method_name.data(db);
                let mut sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("`{method_name}` is ambiguous"),
                    span: primary.resolve(db),
                }];

                for span in cand_spans {
                    sub_diagnostics.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("`{method_name}` is defined here"),
                        span: span.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "ambiguous method call".to_string(),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }

            Self::AmbiguousTrait {
                primary,
                method_name,
                traits,
            } => {
                let method_name = method_name.data(db);
                let mut sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("`{method_name}` is ambiguous"),
                    span: primary.resolve(db),
                }];

                for trait_ in traits {
                    let trait_name = trait_.name(db).unwrap().data(db);
                    sub_diagnostics.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("candidate: `{trait_name}::{method_name}`"),
                        span: primary.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "multiple trait candidates found".to_string(),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }

            Self::AmbiguousTraitInst { primary, cands } => {
                let mut sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "multiple implementations are found".to_string(),
                    span: primary.resolve(db),
                }];

                for cand in cands {
                    sub_diagnostics.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: format!("candidate: {}", cand.pretty_print(db, false)),
                        span: primary.resolve(db), // TODO cand span??
                    });
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "ambiguous trait implementation".to_string(),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }

            Self::InvisibleAmbiguousTrait { primary, traits } => {
                let mut sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "consider importing one of the following traits into the scope to resolve the ambiguity".to_string(),
                    span: primary.resolve(db),
                }];

                for trait_ in traits {
                    if let Some(path) = trait_.scope().pretty_path(db) {
                        sub_diagnostics.push(SubDiagnostic {
                            style: LabelStyle::Secondary,
                            message: format!("`use {path}`"),
                            span: primary.resolve(db),
                        });
                    }
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "trait is not in the scope".to_string(),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }

            Self::MethodNotFound {
                primary,
                method_name,
                receiver,
            } => {
                let (recv_name, recv_ty, recv_kind) = match receiver {
                    Either::Left(ty) => {
                        // Get type information
                        let kind_name = if let Some(adt_ref) = ty.adt_ref(db) {
                            adt_ref.kind_name().to_string()
                        } else if ty.is_func(db) {
                            "fn".to_string()
                        } else {
                            ty.pretty_print(db).to_string()
                        };
                        (ty.pretty_print(db), Some(ty), kind_name)
                    }
                    Either::Right(trait_) => {
                        let name = trait_.trait_(db).name(db).unwrap().data(db);
                        (name, None, "trait".to_string())
                    }
                };

                let method_str = method_name.data(db);
                let message =
                    format!("no method named `{method_str}` found for {recv_kind} `{recv_name}`");

                if let Some(ty) = recv_ty {
                    if let Some(field_ty) =
                        RecordLike::from_ty(*ty).record_field_ty(db, *method_name)
                    {
                        return CompleteDiagnostic {
                            severity: Severity::Error,
                            message,
                            sub_diagnostics: vec![SubDiagnostic {
                                style: LabelStyle::Primary,
                                message: format!(
                                    "field `{}` in `{}` has type `{}`",
                                    method_str,
                                    recv_name,
                                    field_ty.pretty_print(db)
                                ),
                                span: primary.resolve(db),
                            }],
                            notes: vec![],
                            error_code,
                        };
                    }
                }

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message,
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("method not found in `{recv_name}`"),
                        span: primary.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::NotValue { primary, given } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "value is expected".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!(
                        "`{}` cannot be used as a value",
                        match given {
                            Either::Left(item) => item.kind_name(),
                            Either::Right(_) => "type",
                        }
                    ),
                    span: primary.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::TypeAnnotationNeeded { span: primary, ty } => {
                let mut sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "type annotation is needed".to_string(),
                    span: primary.resolve(db),
                }];

                let sub_diag_msg = match ty.base_ty(db).data(db) {
                    TyData::TyVar(var) if var.sort == TyVarSort::Integral => {
                        "no default type is provided for an integer type. consider giving integer type".to_string()
                    }
                    TyData::TyVar(_) => "consider giving `: Type` here".to_string(),
                    _ => format!("consider giving `: {}` here", ty.pretty_print(db)),
                };

                sub_diagnostics.push(SubDiagnostic {
                    style: LabelStyle::Secondary,
                    message: sub_diag_msg,
                    span: primary.resolve(db),
                });

                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "type annotation is needed".to_string(),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }
            BodyDiag::NonExhaustiveMatch {
                primary,
                scrutinee_ty,
                missing_patterns,
            } => {
                let sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "match expression does not cover all possible values".to_string(),
                    span: primary.resolve(db),
                }];
                let notes = if !missing_patterns.is_empty() {
                    let message = if missing_patterns.len() == 1 {
                        format!("Not covered: `{}`", missing_patterns[0])
                    } else {
                        format!("Not covered: `{}`", missing_patterns.join("`, `"))
                    };
                    vec![message]
                } else {
                    vec![]
                };
                CompleteDiagnostic {
                    severity,
                    message: format!(
                        "non-exhaustive patterns: type `{}` is not covered",
                        scrutinee_ty.pretty_print(db)
                    ),
                    sub_diagnostics,
                    notes,
                    error_code,
                }
            }
            BodyDiag::UnreachablePattern { primary } => {
                let sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "this pattern is unreachable".to_string(),
                    span: primary.resolve(db),
                }];
                let notes = vec!["previous patterns already cover all possible values".to_string()];
                CompleteDiagnostic {
                    severity,
                    message: "unreachable pattern".to_string(),
                    sub_diagnostics,
                    notes,
                    error_code,
                }
            }
        }
    }
}

impl DiagnosticVoucher for TraitLowerDiag<'_> {
    fn to_complete(&self, db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic {
        let error_code =
            GlobalErrorCode::new(DiagnosticPass::ImplTraitDefinition, self.local_code());
        match self {
            Self::ExternalTraitForExternalType(impl_trait) => CompleteDiagnostic {
                severity: Severity::Error,
                message: "external trait cannot be implemented for external type".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: "external trait cannot be implemented for external type".to_string(),
                    span: impl_trait.span().resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::ConflictTraitImpl {
                primary,
                conflict_with,
            } => CompleteDiagnostic {
                severity: Severity::Error,
                message: "conflict trait implementation".to_string(),
                sub_diagnostics: vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: "conflict trait implementation".to_string(),
                        span: primary.span().ty().resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: "conflict with this trait implementation".to_string(),
                        span: conflict_with.span().ty().resolve(db),
                    },
                ],
                notes: vec![],
                error_code,
            },

            Self::CyclicSuperTraits(traits) => {
                let span = |t: &TraitDef| t.trait_(db).span().name().resolve(db);
                CompleteDiagnostic {
                    severity: Severity::Error,
                    message: "cyclic trait bounds are not allowed".to_string(),
                    sub_diagnostics: {
                        let mut subs = vec![SubDiagnostic {
                            style: LabelStyle::Primary,
                            message: "trait cycle detected here".to_string(),
                            span: span(traits.first().unwrap()),
                        }];
                        subs.extend(traits.iter().skip(1).map(|t| SubDiagnostic {
                            style: LabelStyle::Secondary,
                            message: "cycle continues here".to_string(),
                            span: span(t),
                        }));
                        subs
                    },
                    notes: vec![],
                    error_code,
                }
            }
        }
    }
}

impl DiagnosticVoucher for TraitConstraintDiag<'_> {
    fn to_complete(&self, db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic {
        let error_code = GlobalErrorCode::new(DiagnosticPass::TraitSatisfaction, self.local_code());
        let severity = Severity::Error;
        match self {
            Self::KindMismatch { primary, trait_def } => CompleteDiagnostic {
                severity,
                message: "type doesn't satisfy required kind bound".to_string(),
                sub_diagnostics: vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: "type doesn't satisfy required kind bound here".to_string(),
                        span: primary.resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: "trait is defined here".to_string(),
                        span: trait_def.span().name().resolve(db),
                    },
                ],
                notes: vec![],
                error_code,
            },

            Self::TraitArgNumMismatch {
                span,
                expected,
                given,
            } => CompleteDiagnostic {
                severity,
                message: "given trait argument number mismatch".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("expected {expected} arguments here, but {given} given"),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::TraitArgKindMismatch {
                span,
                expected,
                actual,
            } => {
                let actual_kind = actual.kind(db);
                let ty_display = actual.pretty_print(db);

                CompleteDiagnostic {
                    severity,
                    message: "given trait argument kind mismatch".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!(
                            "expected `{expected}` kind, but `{ty_display}` has `{actual_kind}` kind",
                        ),
                        span: span.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::TraitBoundNotSat {
                span,
                primary_goal,
                unsat_subgoal,
            } => {
                let msg = format!(
                    "`{}` doesn't implement `{}`",
                    primary_goal.self_ty(db).pretty_print(db),
                    primary_goal.pretty_print(db, false)
                );

                let unsat_subgoal = unsat_subgoal.map(|unsat| {
                    format!(
                        "trait bound `{}` is not satisfied",
                        unsat.pretty_print(db, true)
                    )
                });

                let mut sub_diagnostics = vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: msg.to_string(),
                    span: span.resolve(db),
                }];

                if let Some(subgoal) = unsat_subgoal {
                    sub_diagnostics.push(SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: subgoal.to_string(),
                        span: span.resolve(db),
                    });
                }

                CompleteDiagnostic {
                    severity,
                    message: "trait bound is not satisfied".to_string(),
                    sub_diagnostics,
                    notes: vec![],
                    error_code,
                }
            }

            Self::InfiniteBoundRecursion(span, msg) => CompleteDiagnostic {
                severity,
                message: "infinite trait bound recursion".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: msg.to_string(),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::ConcreteTypeBound(span, ty) => CompleteDiagnostic {
                severity,
                message: "trait bound for concrete type is not allowed".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("`{}` is a concrete type", ty.pretty_print(db)),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::ConstTyBound(span, ty) => CompleteDiagnostic {
                severity,
                message: "trait bound for const type is not allowed".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!("`{}` is a const type", ty.pretty_print(db)),
                    span: span.resolve(db),
                }],
                notes: vec![],
                error_code,
            },
        }
    }
}

impl DiagnosticVoucher for ImplDiag<'_> {
    fn to_complete(&self, db: &dyn SpannedHirAnalysisDb) -> CompleteDiagnostic {
        let error_code = GlobalErrorCode::new(DiagnosticPass::TraitSatisfaction, self.local_code());
        let severity = Severity::Error;

        match self {
            Self::ConflictMethodImpl {
                primary,
                conflict_with,
            } => CompleteDiagnostic {
                severity,
                message: "conflicting method implementations".to_string(),
                sub_diagnostics: vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: "".into(),
                        span: primary.name_span(db).resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: "".into(),
                        span: conflict_with.name_span(db).resolve(db),
                    },
                ],
                notes: vec![],
                error_code,
            },

            Self::MethodNotDefinedInTrait {
                primary,
                trait_,
                method_name,
            } => CompleteDiagnostic {
                severity,
                message: "method not defined in trait".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!(
                        "method `{}` is not defined in trait `{}`",
                        method_name.data(db),
                        trait_.name(db).unwrap().data(db)
                    ),
                    span: primary.resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::NotAllTraitItemsImplemented {
                primary,
                not_implemented,
            } => {
                let missing = not_implemented
                    .iter()
                    .map(|id| id.data(db).as_str())
                    .collect::<Vec<_>>()
                    .join(", ");

                CompleteDiagnostic {
                    severity,
                    message: "not all trait methods are implemented".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!("missing implementations: {missing}"),
                        span: primary.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::MethodTypeParamNumMismatch { trait_m, impl_m } => {
                let impl_params = impl_m.explicit_params(db);
                let trait_params = trait_m.explicit_params(db);

                CompleteDiagnostic {
                    severity,
                    message: "method type parameter count mismatch".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!(
                            "expected {} type parameters, but {} given",
                            trait_params.len(),
                            impl_params.len(),
                        ),
                        span: impl_m.name_span(db).resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::MethodTypeParamKindMismatch {
                trait_m,
                impl_m,
                param_idx,
            } => {
                let message = format!(
                    "expected `{}` kind, but the given type has `{}` kind",
                    trait_m.explicit_params(db)[*param_idx].kind(db),
                    impl_m.explicit_params(db)[*param_idx].kind(db),
                );

                CompleteDiagnostic {
                    severity,
                    message: "method type parameter kind mismatch".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message,
                        span: impl_m
                            .hir_func_def(db)
                            .unwrap()
                            .span()
                            .generic_params()
                            .param(*param_idx)
                            .resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::MethodArgNumMismatch { trait_m, impl_m } => CompleteDiagnostic {
                severity,
                message: "method argument count mismatch".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!(
                        "expected {} arguments, but {} given",
                        trait_m.arg_tys(db).len(),
                        impl_m.arg_tys(db).len(),
                    ),
                    span: impl_m.param_list_span(db).resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::MethodArgLabelMismatch {
                trait_m,
                impl_m,
                param_idx,
            } => CompleteDiagnostic {
                severity,
                message: "method argument label mismatch".to_string(),
                sub_diagnostics: vec![
                    SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: format!(
                            "expected `{}` label, but the given label is `{}`",
                            trait_m
                                .param_label_or_name(db, *param_idx)
                                .unwrap()
                                .pretty_print(db),
                            impl_m
                                .param_label_or_name(db, *param_idx)
                                .unwrap()
                                .pretty_print(db),
                        ),
                        span: impl_m.param_span(db, *param_idx).resolve(db),
                    },
                    SubDiagnostic {
                        style: LabelStyle::Secondary,
                        message: "argument label defined here".to_string(),
                        span: trait_m.param_span(db, *param_idx).resolve(db),
                    },
                ],
                notes: vec![],
                error_code,
            },

            Self::MethodArgTyMismatch {
                trait_m: _,
                impl_m,
                trait_m_ty,
                impl_m_ty,
                param_idx,
            } => CompleteDiagnostic {
                severity,
                message: "method argument type mismatch".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!(
                        "expected `{}` type, but the given type is `{}`",
                        trait_m_ty.pretty_print(db),
                        impl_m_ty.pretty_print(db)
                    ),
                    span: impl_m.param_span(db, *param_idx).resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::MethodRetTyMismatch {
                trait_m: _,
                impl_m,
                trait_ty,
                impl_ty,
            } => CompleteDiagnostic {
                severity,
                message: "method return type mismatch".to_string(),
                sub_diagnostics: vec![SubDiagnostic {
                    style: LabelStyle::Primary,
                    message: format!(
                        "expected `{}` type, but the given type is `{}`",
                        trait_ty.pretty_print(db),
                        impl_ty.pretty_print(db),
                    ),
                    span: impl_m.hir_func_def(db).unwrap().span().ret_ty().resolve(db),
                }],
                notes: vec![],
                error_code,
            },

            Self::MethodStricterBound {
                span,
                stricter_bounds,
            } => {
                // TODO sort!
                // unsatisfied_goals.sort_by_key(|goal| goal.self_ty(db).pretty_print(db));

                let message = format!(
                    "method has stricter bounds than the declared method in the trait: {}",
                    stricter_bounds
                        .iter()
                        .map(|pred| format!("`{}`", pred.pretty_print(db, true)))
                        .join(", ")
                );
                CompleteDiagnostic {
                    severity,
                    message: "method has stricter bounds than trait".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: message.clone(),
                        span: span.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::InvalidSelfType {
                span,
                expected,
                given,
            } => {
                let message = if expected.is_trait_self(db) {
                    format!(
                        "type of `self` must start with `Self`, but the given type is `{}`",
                        given.pretty_print(db),
                    )
                } else {
                    format!(
                        "type of `self` must start with `Self` or `{}`, but the given type is `{}`",
                        expected.pretty_print(db),
                        given.pretty_print(db),
                    )
                };

                CompleteDiagnostic {
                    severity,
                    message: "invalid type for `self` parameter".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message,
                        span: span.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }

            Self::InherentImplIsNotAllowed {
                primary,
                ty,
                is_nominal,
            } => {
                let msg = if *is_nominal {
                    format!("inherent impl is not allowed for foreign type `{ty}`")
                } else {
                    "inherent impl is not allowed for non nominal type".to_string()
                };

                CompleteDiagnostic {
                    severity,
                    message: "invalid inherent implementation".to_string(),
                    sub_diagnostics: vec![SubDiagnostic {
                        style: LabelStyle::Primary,
                        message: msg,
                        span: primary.resolve(db),
                    }],
                    notes: vec![],
                    error_code,
                }
            }
        }
    }
}
