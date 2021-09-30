use crate::builtins;
use crate::context::Analysis;
use crate::db::AnalyzerDb;
use crate::errors;
use crate::namespace::items::{
    Contract, ContractId, Function, ModuleId, NamedItem, Struct, StructId, TypeAlias, TypeDef,
};
use crate::namespace::types;
use fe_common::diagnostics::Label;
use fe_parser::ast;
use indexmap::map::{Entry, IndexMap};
use std::rc::Rc;
use strum::IntoEnumIterator;

// Placeholder; someday std::prelude will be a proper module.
fn std_prelude_items() -> Vec<NamedItem> {
    let mut items = vec![
        NamedItem::BuiltinFunction(builtins::GlobalMethod::Keccak256),
        NamedItem::Type(TypeDef::Primitive(types::Base::Bool)),
        NamedItem::Type(TypeDef::Primitive(types::Base::Address)),
    ];
    items.extend(
        types::Integer::iter()
            .map(|typ| NamedItem::Type(TypeDef::Primitive(types::Base::Numeric(typ)))),
    );
    items.extend(types::GenericType::iter().map(NamedItem::GenericType));
    items.extend(builtins::Object::iter().map(NamedItem::Object));
    items
}

// This tentatively includes all imported items as well as those defined in the module
pub fn module_all_named_items(db: &dyn AnalyzerDb, module: ModuleId) -> Rc<Vec<NamedItem>> {
    let ast::Module { body } = &module.data(db).ast;

    let mut items = std_prelude_items();
    items.extend(body.iter().filter_map(|stmt| match stmt {
        ast::ModuleStmt::TypeAlias(node) => Some(NamedItem::Type(TypeDef::Alias(
            db.intern_type_alias(Rc::new(TypeAlias {
                ast: node.clone(),
                module,
            })),
        ))),
        ast::ModuleStmt::Contract(node) => Some(NamedItem::Type(TypeDef::Contract(
            db.intern_contract(Rc::new(Contract {
                name: node.name().to_string(),
                ast: node.clone(),
                module,
            })),
        ))),
        ast::ModuleStmt::Struct(node) => Some(NamedItem::Type(TypeDef::Struct(db.intern_struct(
            Rc::new(Struct {
                ast: node.clone(),
                module,
            }),
        )))),
        ast::ModuleStmt::Function(node) => {
            Some(NamedItem::Function(db.intern_function(Rc::new(Function {
                ast: node.clone(),
                module,
                contract: None,
            }))))
        }
        ast::ModuleStmt::Pragma(_) => None,
        ast::ModuleStmt::Import(_) => todo!(),
    }));
    Rc::new(items)
}

pub fn module_named_item_map(
    db: &dyn AnalyzerDb,
    module: ModuleId,
) -> Analysis<Rc<IndexMap<String, NamedItem>>> {
    let mut diagnostics = vec![];

    let mut map = IndexMap::<String, NamedItem>::new();
    for item in module.all_named_items(db).iter() {
        match map.entry(item.name(db)) {
            Entry::Occupied(entry) => {
                if entry.get().is_builtin() {
                    let builtin_kind = entry.get().item_kind_display_name();
                    diagnostics.push(errors::error(
                        &format!("type name conflicts with built-in {}", builtin_kind),
                        item.name_span(db).expect("duplicate built-in names?"),
                        &format!("`{}` is a built-in {}", entry.key(), builtin_kind),
                    ));
                } else {
                    diagnostics.push(errors::fancy_error(
                        "duplicate type name",
                        vec![
                            Label::primary(
                                entry.get().span(db).unwrap(),
                                format!("`{}` first defined here", entry.key()),
                            ),
                            Label::secondary(
                                item.span(db)
                                    .expect("built-in conflicts with user-defined name?"),
                                format!("`{}` redefined here", entry.key()),
                            ),
                        ],
                        vec![],
                    ));
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(*item);
            }
        }
    }
    Analysis {
        value: Rc::new(map),
        diagnostics: Rc::new(diagnostics),
    }
}

pub fn module_all_type_defs(db: &dyn AnalyzerDb, module: ModuleId) -> Rc<Vec<TypeDef>> {
    let ast::Module { body } = &module.data(db).ast;
    let ids = body
        .iter()
        .filter_map(|stmt| match stmt {
            ast::ModuleStmt::TypeAlias(node) => {
                Some(TypeDef::Alias(db.intern_type_alias(Rc::new(TypeAlias {
                    ast: node.clone(),
                    module,
                }))))
            }
            ast::ModuleStmt::Contract(node) => {
                Some(TypeDef::Contract(db.intern_contract(Rc::new(Contract {
                    name: node.name().to_string(),
                    ast: node.clone(),
                    module,
                }))))
            }
            ast::ModuleStmt::Struct(node) => {
                Some(TypeDef::Struct(db.intern_struct(Rc::new(Struct {
                    ast: node.clone(),
                    module,
                }))))
            }
            _ => None,
        })
        .collect();
    Rc::new(ids)
}

pub fn module_type_def_map(
    db: &dyn AnalyzerDb,
    module: ModuleId,
) -> Analysis<Rc<IndexMap<String, TypeDef>>> {
    let mut diagnostics = vec![];

    let mut map = IndexMap::<String, TypeDef>::new();
    for def in module.all_type_defs(db).iter() {
        let def_name = def.name(db);
        if let Some(reserved) = builtins::reserved_name(&def_name) {
            diagnostics.push(errors::error(
                &format!("type name conflicts with built-in {}", reserved.as_ref()),
                def.name_span(db),
                &format!("`{}` is a built-in {}", def_name, reserved.as_ref()),
            ));
            continue;
        }

        match map.entry(def.name(db)) {
            Entry::Occupied(entry) => {
                diagnostics.push(errors::fancy_error(
                    "duplicate type name",
                    vec![
                        Label::primary(
                            entry.get().span(db),
                            format!("`{}` first defined here", entry.key()),
                        ),
                        Label::secondary(def.span(db), format!("`{}` redefined here", entry.key())),
                    ],
                    vec![],
                ));
            }
            Entry::Vacant(entry) => {
                entry.insert(*def);
            }
        }
    }
    Analysis {
        value: Rc::new(map),
        diagnostics: Rc::new(diagnostics),
    }
}

// XXX use named_items? return TypeError::NotAType?
pub fn module_resolve_type(
    db: &dyn AnalyzerDb,
    module: ModuleId,
    name: String,
) -> Option<Result<types::Type, errors::TypeError>> {
    Some(module.type_defs(db).get(&name)?.typ(db))
}

#[allow(clippy::ptr_arg)]
pub fn module_resolve_type_cycle(
    _db: &dyn AnalyzerDb,
    _cycle: &[String],
    _module: &ModuleId,
    _name: &String,
) -> Option<Result<types::Type, errors::TypeError>> {
    // The only possible type cycle currently is a recursive type alias,
    // which is handled in queries/types.rs
    // However, salsa will also call this function if there's such a cycle,
    // so we can't panic here, and we can't return a TypeError because
    // there's no way to emit a diagnostic! The only option is to return
    // None, and handle type cycles in more specifc cycle handlers.
    None
}

pub fn module_contracts(db: &dyn AnalyzerDb, module: ModuleId) -> Rc<Vec<ContractId>> {
    let defs = module.all_type_defs(db);
    Rc::new(
        defs.iter()
            .filter_map(|def| match def {
                TypeDef::Contract(id) => Some(*id),
                _ => None,
            })
            .collect(),
    )
}

pub fn module_structs(db: &dyn AnalyzerDb, module: ModuleId) -> Rc<Vec<StructId>> {
    let defs = module.all_type_defs(db);
    Rc::new(
        defs.iter()
            .filter_map(|def| match def {
                TypeDef::Struct(id) => Some(*id),
                _ => None,
            })
            .collect(),
    )
}
