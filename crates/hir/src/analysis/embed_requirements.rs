use std::collections::{HashMap, HashSet};

use crate::analysis::HirAnalysisDb;
use crate::hir_def::{Attr, AttrArgValue, ItemKind, TopLevelMod};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct OperatorRequirement {
    trait_path: &'static str,
    method: &'static str,
    symbol: &'static str,
}

const OPERATOR_REQUIREMENTS: &[OperatorRequirement] = &[
    OperatorRequirement {
        trait_path: "core::ops::Neg",
        method: "neg",
        symbol: "-",
    },
    OperatorRequirement {
        trait_path: "core::ops::Not",
        method: "not",
        symbol: "!",
    },
    OperatorRequirement {
        trait_path: "core::ops::BitNot",
        method: "bit_not",
        symbol: "~",
    },
    OperatorRequirement {
        trait_path: "core::ops::Add",
        method: "add",
        symbol: "+",
    },
    OperatorRequirement {
        trait_path: "core::ops::Sub",
        method: "sub",
        symbol: "-",
    },
    OperatorRequirement {
        trait_path: "core::ops::Mul",
        method: "mul",
        symbol: "*",
    },
    OperatorRequirement {
        trait_path: "core::ops::Div",
        method: "div",
        symbol: "/",
    },
    OperatorRequirement {
        trait_path: "core::ops::Rem",
        method: "rem",
        symbol: "%",
    },
    OperatorRequirement {
        trait_path: "core::ops::Pow",
        method: "pow",
        symbol: "**",
    },
    OperatorRequirement {
        trait_path: "core::ops::Shl",
        method: "shl",
        symbol: "<<",
    },
    OperatorRequirement {
        trait_path: "core::ops::Shr",
        method: "shr",
        symbol: ">>",
    },
    OperatorRequirement {
        trait_path: "core::ops::BitAnd",
        method: "bitand",
        symbol: "&",
    },
    OperatorRequirement {
        trait_path: "core::ops::BitOr",
        method: "bitor",
        symbol: "|",
    },
    OperatorRequirement {
        trait_path: "core::ops::BitXor",
        method: "bitxor",
        symbol: "^",
    },
    OperatorRequirement {
        trait_path: "core::ops::Eq",
        method: "eq",
        symbol: "==",
    },
    OperatorRequirement {
        trait_path: "core::ops::Eq",
        method: "ne",
        symbol: "!=",
    },
    OperatorRequirement {
        trait_path: "core::ops::Ord",
        method: "lt",
        symbol: "<",
    },
    OperatorRequirement {
        trait_path: "core::ops::Ord",
        method: "le",
        symbol: "<=",
    },
    OperatorRequirement {
        trait_path: "core::ops::Ord",
        method: "gt",
        symbol: ">",
    },
    OperatorRequirement {
        trait_path: "core::ops::Ord",
        method: "ge",
        symbol: ">=",
    },
    OperatorRequirement {
        trait_path: "core::ops::Index",
        method: "index",
        symbol: "[]",
    },
    OperatorRequirement {
        trait_path: "core::ops::AddAssign",
        method: "add_assign",
        symbol: "+=",
    },
    OperatorRequirement {
        trait_path: "core::ops::SubAssign",
        method: "sub_assign",
        symbol: "-=",
    },
    OperatorRequirement {
        trait_path: "core::ops::MulAssign",
        method: "mul_assign",
        symbol: "*=",
    },
    OperatorRequirement {
        trait_path: "core::ops::DivAssign",
        method: "div_assign",
        symbol: "/=",
    },
    OperatorRequirement {
        trait_path: "core::ops::RemAssign",
        method: "rem_assign",
        symbol: "%=",
    },
    OperatorRequirement {
        trait_path: "core::ops::PowAssign",
        method: "pow_assign",
        symbol: "**=",
    },
    OperatorRequirement {
        trait_path: "core::ops::ShlAssign",
        method: "shl_assign",
        symbol: "<<=",
    },
    OperatorRequirement {
        trait_path: "core::ops::ShrAssign",
        method: "shr_assign",
        symbol: ">>=",
    },
    OperatorRequirement {
        trait_path: "core::ops::BitAndAssign",
        method: "bitand_assign",
        symbol: "&=",
    },
    OperatorRequirement {
        trait_path: "core::ops::BitOrAssign",
        method: "bitor_assign",
        symbol: "|=",
    },
    OperatorRequirement {
        trait_path: "core::ops::BitXorAssign",
        method: "bitxor_assign",
        symbol: "^=",
    },
];

pub fn check_embed_operator_annotations<'db>(
    db: &'db dyn HirAnalysisDb,
    top_mod: TopLevelMod<'db>,
) -> Vec<String> {
    let expected: HashMap<(&'static str, &'static str), &'static str> = OPERATOR_REQUIREMENTS
        .iter()
        .map(|req| ((req.trait_path, req.method), req.symbol))
        .collect();

    let mut seen: HashMap<(String, String), String> = HashMap::new();
    let mut errors = Vec::new();

    for item in top_mod.all_items(db).iter() {
        let ItemKind::Use(use_) = item else {
            continue;
        };
        let Some(attributes) = ItemKind::Use(*use_).attrs(db) else {
            continue;
        };
        let trait_path = use_.pretty_path(db);

        for attr in attributes.data(db).iter() {
            let Attr::Normal(attr) = attr else {
                continue;
            };
            let Some(path) = attr.path.to_opt() else {
                continue;
            };
            let Some(ident) = path.as_ident(db) else {
                continue;
            };
            if ident.data(db) != "operator" {
                continue;
            }
            if use_.is_glob(db) {
                errors.push(format!(
                    "operator annotations must be on a concrete use path, got `{trait_path}::*`"
                ));
                continue;
            }
            if attr.args.is_empty() {
                errors.push(format!(
                    "operator annotation on `{trait_path}` is missing method bindings"
                ));
                continue;
            }

            for arg in attr.args.iter() {
                let Some(method) = arg.key_str(db) else {
                    errors.push(format!(
                        "operator annotation on `{trait_path}` has an invalid method key"
                    ));
                    continue;
                };
                let Some(value) = &arg.value else {
                    errors.push(format!(
                        "operator annotation for `{trait_path}::{method}` is missing a symbol"
                    ));
                    continue;
                };

                let symbol = match value {
                    AttrArgValue::Lit(lit) => match lit {
                        crate::hir_def::LitKind::String(symbol) => symbol.data(db).clone(),
                        _ => {
                            errors.push(format!(
                                "operator annotation for `{trait_path}::{method}` must use a string literal"
                            ));
                            continue;
                        }
                    },
                    AttrArgValue::Ident(_) => {
                        errors.push(format!(
                            "operator annotation for `{trait_path}::{method}` must use a string literal"
                        ));
                        continue;
                    }
                };

                let key = (trait_path.clone(), method.to_string());
                if let Some(existing) = seen.insert(key.clone(), symbol.clone())
                    && existing != symbol
                {
                    errors.push(format!(
                        "operator annotation for `{trait_path}::{method}` conflicts with `{existing}`"
                    ));
                }
            }
        }
    }

    let mut unknown = Vec::new();
    let mut missing = Vec::new();
    let mut checked: HashSet<(String, String)> = HashSet::new();

    for ((trait_path, method), symbol) in &seen {
        if let Some(expected_symbol) = expected.get(&(trait_path.as_str(), method.as_str())) {
            checked.insert((trait_path.clone(), method.clone()));
            if symbol != expected_symbol {
                errors.push(format!(
                    "operator annotation for `{trait_path}::{method}` must use `{expected_symbol}`, got `{symbol}`"
                ));
            }
        } else {
            unknown.push(format!("{trait_path}::{method}"));
        }
    }

    for req in OPERATOR_REQUIREMENTS {
        let key = (req.trait_path.to_string(), req.method.to_string());
        if !checked.contains(&key) {
            missing.push(format!(
                "missing operator annotation for `{}` (`{}`)",
                req.symbol, req.trait_path
            ));
        }
    }

    if !unknown.is_empty() {
        unknown.sort();
        for entry in unknown {
            errors.push(format!("unknown operator annotation for `{entry}`"));
        }
    }

    if !missing.is_empty() {
        errors.extend(missing);
    }

    errors
}
