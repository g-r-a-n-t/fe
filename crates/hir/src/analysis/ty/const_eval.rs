use num_bigint::BigUint;
use rustc_hash::FxHashSet;

use crate::analysis::{
    HirAnalysisDb,
    name_resolution::{PathRes, resolve_path},
    ty::{
        trait_def::assoc_const_body_for_trait_inst, trait_resolution::PredicateListId,
        ty_check::ConstRef,
    },
};
use crate::core::hir_def::{Body, Expr, LitKind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstValue {
    Int(BigUint),
    Bool(bool),
}

pub fn try_eval_const_body<'db>(db: &'db dyn HirAnalysisDb, body: Body<'db>) -> Option<ConstValue> {
    let mut visited = FxHashSet::default();
    let expr = body.expr(db).data(db, body).borrowed().to_opt()?;
    try_eval_expr(db, body, expr.clone(), &mut visited)
}

pub fn try_eval_const_ref<'db>(
    db: &'db dyn HirAnalysisDb,
    cref: ConstRef<'db>,
) -> Option<ConstValue> {
    let mut visited = FxHashSet::default();
    try_eval_const_ref_inner(db, cref, &mut visited)
}

fn try_eval_const_ref_inner<'db>(
    db: &'db dyn HirAnalysisDb,
    cref: ConstRef<'db>,
    visited: &mut FxHashSet<ConstRef<'db>>,
) -> Option<ConstValue> {
    if !visited.insert(cref) {
        return None;
    }

    let result = match cref {
        ConstRef::Const(const_def) => {
            let body = const_def.body(db).to_opt()?;
            let expr = body.expr(db).data(db, body).borrowed().to_opt()?;
            try_eval_expr(db, body, expr.clone(), visited)
        }
        ConstRef::TraitConst { inst, name } => {
            let body = assoc_const_body_for_trait_inst(db, inst, name).or_else(|| {
                let trait_ = inst.def(db);
                trait_.const_(db, name).and_then(|c| c.default_body(db))
            })?;
            let expr = body.expr(db).data(db, body).borrowed().to_opt()?;
            try_eval_expr(db, body, expr.clone(), visited)
        }
    };

    visited.remove(&cref);
    result
}

fn try_eval_expr<'db>(
    db: &'db dyn HirAnalysisDb,
    body: Body<'db>,
    expr: Expr<'db>,
    visited: &mut FxHashSet<ConstRef<'db>>,
) -> Option<ConstValue> {
    match expr {
        Expr::Lit(LitKind::Int(value)) => Some(ConstValue::Int(value.data(db).clone())),
        Expr::Lit(LitKind::Bool(flag)) => Some(ConstValue::Bool(flag)),
        Expr::Path(path) => {
            let path = path.to_opt()?;
            let assumptions = PredicateListId::empty_list(db);
            match resolve_path(db, path, body.scope(), assumptions, true).ok()? {
                PathRes::Const(const_def, _ty) => {
                    try_eval_const_ref_inner(db, ConstRef::Const(const_def), visited)
                }
                PathRes::TraitConst(_ty, inst, name) => {
                    try_eval_const_ref_inner(db, ConstRef::TraitConst { inst, name }, visited)
                }
                _ => None,
            }
        }
        _ => None,
    }
}
