use crate::builtins;
use crate::context::{Analysis, AnalyzerContext};
use crate::db::AnalyzerDb;
use crate::errors::{self, TypeError};
use crate::namespace::items::{
    Contract, ContractId, Function, Item, ModuleConstant, ModuleConstantId, ModuleId, Struct,
    StructId, TypeAlias, TypeDef,
};
use crate::namespace::scopes::ItemScope;
use crate::namespace::types::{self, Type};
use crate::traversal::types::type_desc;
use fe_common::diagnostics::Label;
use fe_parser::ast;
use indexmap::indexmap;
use indexmap::map::{Entry, IndexMap};
use std::rc::Rc;
use strum::IntoEnumIterator;

// Placeholder; someday std::prelude will be a proper module.
fn std_prelude_items() -> IndexMap<String, Item> {
    let mut items = indexmap! {
        "bool".to_string() => Item::Type(TypeDef::Primitive(types::Base::Bool)),
        "address".to_string() => Item::Type(TypeDef::Primitive(types::Base::Address)),
    };
    items.extend(types::Integer::iter().map(|typ| {
        (
            typ.as_ref().to_string(),
            Item::Type(TypeDef::Primitive(types::Base::Numeric(typ))),
        )
    }));
    items.extend(
        types::GenericType::iter().map(|typ| (typ.name().to_string(), Item::GenericType(typ))),
    );
    items.extend(
        builtins::GlobalFunction::iter()
            .map(|fun| (fun.as_ref().to_string(), Item::BuiltinFunction(fun))),
    );
    items.extend(
        builtins::GlobalObject::iter().map(|obj| (obj.as_ref().to_string(), Item::Object(obj))),
    );
    items
}

pub fn module_used_item_map(db: &dyn AnalyzerDb, module: ModuleId) -> Rc<IndexMap<String, Item>> {
    let ast::Module { body } = &module.data(db).ast;

    let items = body
        .iter()
        .fold(indexmap! {}, |accum, stmt| {
            if let ast::ModuleStmt::Use(use_stmt) = stmt {
                let items = resolve_use_tree(
                    db,
                    module
                        .parent_module(db)
                        .expect(&format!("no parent for {}", module.name(db))),
                    &use_stmt.kind.tree.kind,
                );
                accum.into_iter().chain(items).collect::<IndexMap<_, _>>()
            } else {
                accum
            }
        })
        .into_iter()
        .chain(std_prelude_items())
        .collect::<IndexMap<_, _>>();

    Rc::new(items)
}

fn resolve_use_tree(
    db: &dyn AnalyzerDb,
    module: ModuleId,
    tree: &ast::UseTree,
) -> IndexMap<String, Item> {
    match tree {
        ast::UseTree::Glob { prefix } => {
            let prefix = path_names(&prefix.kind);
            let prefix_item = module.resolve_sub_path(db, &prefix).unwrap();

            let prefix_module = if let Item::Module(module) = prefix_item {
                module
            } else {
                panic!("not a module")
            };

            (*prefix_module.items(db)).clone()
        }
        ast::UseTree::Nested { prefix, children } => {
            let prefix = path_names(&prefix.kind);
            let prefix_item = module.resolve_sub_path(db, &prefix).unwrap();

            let prefix_module = if let Item::Module(module) = prefix_item {
                module
            } else {
                panic!("not a module")
            };

            let items = children.iter().fold(indexmap! {}, |accum, node| {
                let child_items = resolve_use_tree(db, prefix_module, &node.kind);
                accum
                    .into_iter()
                    .chain(child_items)
                    .collect::<IndexMap<_, _>>()
            });

            items
        }
        ast::UseTree::Simple { path, rename } => {
            let path = path_names(&path.kind);
            let item = module.resolve_sub_path(db, &path).unwrap();

            let item_name = if let Some(name) = rename {
                name.kind.clone()
            } else {
                item.name(db)
            };

            indexmap! { item_name => item }
        }
    }
}

fn path_names(path: &ast::Path) -> Vec<String> {
    path.names.iter().map(|node| node.kind.clone()).collect()
}

pub fn module_all_items(db: &dyn AnalyzerDb, module: ModuleId) -> Rc<Vec<Item>> {
    let ast::Module { body } = &module.data(db).ast;

    let items = body
        .iter()
        .filter_map(|stmt| match stmt {
            ast::ModuleStmt::TypeAlias(node) => Some(Item::Type(TypeDef::Alias(
                db.intern_type_alias(Rc::new(TypeAlias {
                    ast: node.clone(),
                    module,
                })),
            ))),
            ast::ModuleStmt::Contract(node) => Some(Item::Type(TypeDef::Contract(
                db.intern_contract(Rc::new(Contract {
                    name: node.name().to_string(),
                    ast: node.clone(),
                    module,
                })),
            ))),
            ast::ModuleStmt::Struct(node) => Some(Item::Type(TypeDef::Struct(db.intern_struct(
                Rc::new(Struct {
                    ast: node.clone(),
                    module,
                }),
            )))),
            ast::ModuleStmt::Constant(node) => Some(Item::Constant(db.intern_module_const(
                Rc::new(ModuleConstant {
                    ast: *node.clone(),
                    module,
                }),
            ))),
            ast::ModuleStmt::Function(node) => {
                Some(Item::Function(db.intern_function(Rc::new(Function {
                    ast: node.clone(),
                    module,
                    parent: None,
                }))))
            }
            ast::ModuleStmt::Pragma(_) => None,
            ast::ModuleStmt::Use(_) => None,
        })
        .collect();
    Rc::new(items)
}

pub fn module_item_map(
    db: &dyn AnalyzerDb,
    module: ModuleId,
) -> Analysis<Rc<IndexMap<String, Item>>> {
    let mut diagnostics = vec![];

    let builtin_items = std_prelude_items();
    let sub_modules = module
        .sub_modules(db)
        .iter()
        .map(|(name, id)| (name.clone(), Item::Module(*id)))
        .collect::<IndexMap<_, _>>();
    let mut map = IndexMap::<String, Item>::new();

    for item in module.all_items(db).iter() {
        let item_name = item.name(db);
        if let Some(builtin) = builtin_items.get(&item_name) {
            let builtin_kind = builtin.item_kind_display_name();
            diagnostics.push(errors::error(
                &format!("type name conflicts with built-in {}", builtin_kind),
                item.name_span(db).expect("duplicate built-in names?"),
                &format!("`{}` is a built-in {}", item_name, builtin_kind),
            ));
            continue;
        }

        match map.entry(item_name) {
            Entry::Occupied(entry) => {
                diagnostics.push(errors::fancy_error(
                    "duplicate type name",
                    vec![
                        Label::primary(
                            entry.get().name_span(db).unwrap(),
                            format!("`{}` first defined here", entry.key()),
                        ),
                        Label::secondary(
                            item.name_span(db)
                                .expect("built-in conflicts with user-defined name?"),
                            format!("`{}` redefined here", entry.key()),
                        ),
                    ],
                    vec![],
                ));
            }
            Entry::Vacant(entry) => {
                entry.insert(*item);
            }
        }
    }
    Analysis {
        value: Rc::new(
            map.into_iter()
                .chain(sub_modules)
                .collect::<IndexMap<_, _>>(),
        ),
        diagnostics: Rc::new(diagnostics),
    }
}

pub fn module_contracts(db: &dyn AnalyzerDb, module: ModuleId) -> Rc<Vec<ContractId>> {
    Rc::new(
        module
            .all_items(db)
            .iter()
            .filter_map(|item| match item {
                Item::Type(TypeDef::Contract(id)) => Some(*id),
                _ => None,
            })
            .collect(),
    )
}

pub fn module_structs(db: &dyn AnalyzerDb, module: ModuleId) -> Rc<Vec<StructId>> {
    Rc::new(
        module
            .all_items(db)
            .iter()
            // TODO: figure out better pattern
            .chain(module.used_items(db).values())
            .filter_map(|item| match item {
                Item::Type(TypeDef::Struct(id)) => Some(*id),
                _ => None,
            })
            .collect(),
    )
}

pub fn module_constant_type(
    db: &dyn AnalyzerDb,
    constant: ModuleConstantId,
) -> Analysis<Result<types::Type, TypeError>> {
    let mut scope = ItemScope::new(db, constant.data(db).module);
    let typ = type_desc(&mut scope, &constant.data(db).ast.kind.typ);

    match &typ {
        Ok(typ) if !matches!(typ, Type::Base(_)) => {
            scope.error(
                "Non-base types not yet supported for constants",
                constant.data(db).ast.kind.typ.span,
                &format!("this has type `{}`; expected a primitive type", typ),
            );
        }
        _ => {}
    }

    Analysis {
        value: typ,
        diagnostics: Rc::new(scope.diagnostics),
    }
}
