//! Shared utility helpers used across the Yul emitter modules.

use driver::DriverDataBase;
use hir::hir_def::{Func, HirIngot, item::ItemKind, scope_graph::ScopeId};

use super::YulError;

pub(super) fn prefix_yul_name(name: &str) -> String {
    if name.starts_with('$') {
        name.to_string()
    } else {
        format!("${name}")
    }
}

pub(super) fn is_std_evm_ops(db: &DriverDataBase, func: Func<'_>) -> bool {
    if func.body(db).is_some() {
        return false;
    }

    let ingot = func.top_mod(db).ingot(db);
    let root_mod = ingot.root_mod(db);

    let mut path = Vec::new();
    let mut scope = func.scope();
    while let Some(parent) = scope.parent_module(db) {
        match parent {
            ScopeId::Item(ItemKind::Mod(mod_)) => {
                if let Some(name) = mod_.name(db).to_opt() {
                    path.push(name.data(db).to_string());
                }
            }
            ScopeId::Item(ItemKind::TopMod(top_mod)) => {
                if top_mod != root_mod {
                    path.push(top_mod.name(db).data(db).to_string());
                }
            }
            _ => {}
        }
        scope = parent;
    }
    path.reverse();

    path.last().is_some_and(|seg| seg == "ops")
        && path.iter().rev().nth(1).is_some_and(|seg| seg == "evm")
}

/// Returns the display name of a function or `<anonymous>` if one does not exist.
///
/// * `func` - HIR function to name.
///
/// Returns the display string used for diagnostics and Yul names.
pub(super) fn function_name(db: &DriverDataBase, func: Func<'_>) -> String {
    func.name(db)
        .to_opt()
        .map(|id| id.data(db).to_string())
        .unwrap_or_else(|| "<anonymous>".into())
}

/// Converts usages of cast shims into their lone argument so we don't emit fake calls.
///
/// * `name` - Function identifier for the shim.
/// * `args` - Already-lowered argument expressions.
///
/// Returns the collapsed argument when `name` is a shim, otherwise `None`.
pub(super) fn try_collapse_cast_shim(
    name: &str,
    args: &[String],
) -> Result<Option<String>, YulError> {
    if !is_cast_shim(name) {
        return Ok(None);
    }
    debug_assert_eq!(
        args.len(),
        1,
        "cast shims are expected to take a single argument"
    );
    let arg = args
        .first()
        .cloned()
        .ok_or_else(|| YulError::Unsupported("cast shim missing argument".into()))?;
    Ok(Some(arg))
}

/// Returns `true` when `name` matches one of the temporary casting shims
/// (`__{src}_as_{dst}`) used while the `as` syntax is unavailable.
fn is_cast_shim(name: &str) -> bool {
    let name = name.strip_prefix('$').unwrap_or(name);
    cast_shim_parts(name).is_some()
}

/// Validates that a name follows the `__{src}_as_{dst}` convention and returns the parts.
fn cast_shim_parts(name: &str) -> Option<(&str, &str)> {
    let stripped = name.strip_prefix("__")?;
    let (src, dst) = stripped.split_once("_as_")?;
    if src.is_empty() || dst.is_empty() {
        return None;
    }
    if !is_cast_ident(src) || !is_cast_ident(dst) {
        return None;
    }
    Some((src, dst))
}

/// Validates that a substring of a shim name matches the allowed identifier schema.
fn is_cast_ident(part: &str) -> bool {
    part.chars()
        .all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit())
}
