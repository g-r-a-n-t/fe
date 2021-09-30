use crate::context::{AnalyzerContext, NamedThing};
use crate::errors::TypeError;
use crate::namespace::items::Item;
use crate::namespace::types::{
    Array, FixedSize, GenericArg, GenericParamKind, GenericType, Tuple, Type,
};
use crate::traversal::call_args::validate_arg_count;
use fe_common::diagnostics::Label;
use fe_common::utils::humanize::pluralize_conditionally;
use fe_common::Spanned;
use fe_parser::ast;
use fe_parser::node::{Node, Span};
use std::convert::TryFrom;
use vec1::Vec1;

pub fn apply_generic_type_args(
    context: &mut dyn AnalyzerContext,
    generic: GenericType,
    name_span: Span,
    args: Option<&Node<Vec<ast::GenericArg>>>,
) -> Result<Type, TypeError> {
    let params = generic.params();

    let args = args.ok_or_else(|| {
        TypeError::new(context.fancy_error(
            &format!(
                "missing generic {} for type `{}`",
                pluralize_conditionally("argument", params.len()),
                generic.name()
            ),
            vec![Label::primary(
                name_span,
                &format!(
                    "expected {} generic {}",
                    params.len(),
                    pluralize_conditionally("argument", params.len())
                ),
            )],
            vec![friendly_generic_arg_example_string(generic)],
        ))
    })?;

    if let Some(diag) = validate_arg_count(
        context,
        generic.name(),
        name_span,
        args,
        params.len(),
        "generic argument",
    ) {
        return Err(TypeError::new(diag));
    }

    let concrete_args = params
        .iter()
        .zip(args.kind.iter())
        .map(|(param, arg)| match (param.kind, arg) {
            (GenericParamKind::Int, ast::GenericArg::Int(int_node)) => {
                Ok(GenericArg::Int(int_node.kind))
            }
            (GenericParamKind::Int, ast::GenericArg::TypeDesc(_)) => {
                Err(TypeError::new(context.fancy_error(
                    &format!("`{}` {} must be an integer", generic.name(), param.name),
                    vec![Label::primary(arg.span(), "expected an integer")],
                    vec![],
                )))
            }
            (GenericParamKind::PrimitiveType, ast::GenericArg::TypeDesc(type_node)) => {
                match type_desc(context, type_node)? {
                    Type::Base(base) => Ok(GenericArg::Type(Type::Base(base))),
                    typ => Err(TypeError::new(context.error(
                        &format!(
                            "`{}` {} must be a primitive type",
                            generic.name(),
                            param.name
                        ),
                        type_node.span,
                        &format!("this has type `{}`; expected a primitive type", typ),
                    ))),
                }
            }
            (GenericParamKind::AnyType, ast::GenericArg::TypeDesc(type_node)) => {
                Ok(GenericArg::Type(type_desc(context, type_node)?))
            }
            (
                GenericParamKind::PrimitiveType | GenericParamKind::AnyType,
                ast::GenericArg::Int(_),
            ) => Err(TypeError::new(context.fancy_error(
                &format!("`{}` {} must be a type", generic.name(), param.name),
                vec![Label::primary(arg.span(), "expected a type name")],
                vec![],
            ))),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(generic
        .apply(&concrete_args)
        .expect("failed to construct generic type after checking args"))
}

fn friendly_generic_arg_example_string(generic: GenericType) -> String {
    let example_args = generic
        .params()
        .iter()
        .map(|param| match param.kind {
            GenericParamKind::Int => "32",
            GenericParamKind::PrimitiveType => "u64",
            GenericParamKind::AnyType => "String<32>",
        })
        .collect::<Vec<&'static str>>();

    format!("Example: `{}<{}>`", generic.name(), example_args.join(", "))
}

pub fn resolve_concrete_type(
    context: &mut dyn AnalyzerContext,
    name: &str,
    name_span: Span,
    generic_args: Option<&Node<Vec<ast::GenericArg>>>,
) -> Result<Type, TypeError> {
    let named_item = context.resolve_name(name).ok_or_else(|| {
        TypeError::new(context.error(
            "undefined type",
            name_span,
            &format!("`{}` has not been defined", name),
        ))
    })?;

    match named_item {
        NamedThing::Item(Item::Type(id)) => {
            if let Some(args) = generic_args {
                context.fancy_error(
                    &format!("`{}` type is not generic", name),
                    vec![Label::primary(
                        args.span,
                        "unexpected generic argument list",
                    )],
                    vec![],
                );
            }
            id.typ(context.db())
        }
        NamedThing::Item(Item::GenericType(generic)) => {
            apply_generic_type_args(context, generic, name_span, generic_args)
        }
        _ => Err(TypeError::new(context.fancy_error(
            &format!("`{}` is not a type name", name),
            if let Some(def_span) = named_item.name_span(context.db()) {
                vec![
                    Label::primary(
                        def_span,
                        format!(
                            "`{}` is defined here as a {}",
                            name,
                            named_item.item_kind_display_name()
                        ),
                    ),
                    Label::primary(name_span, format!("`{}` is used here as a type", name)),
                ]
            } else {
                vec![Label::primary(
                    name_span,
                    format!("`{}` is a {}", name, named_item.item_kind_display_name()),
                )]
            },
            vec![],
        ))),
    }
}

// XXX remove?
// pub fn resolve_type_name(
//     context: &mut dyn AnalyzerContext,
//     name: &str,
//     name_span: Span,
//     generic_args: Option<&Node<Vec<ast::GenericArg>>>,
// ) -> Option<Result<Type, TypeError>> {
//     match (name, generic_args) {
//         ("String", Some(args)) => match &args.kind[..] {
//             [ast::GenericArg::Int(len)] => Some(Ok(Type::String(FeString { max_size: len.kind }))),
//             _ => Some(Err(TypeError::new(context.fancy_error(
//                 "invalid `String` type argument",
//                 vec![Label::primary(args.span, "expected an integer")],
//                 vec!["Example: String<100>".into()],
//             )))),
//         },
//         ("String", None) => Some(Err(TypeError::new(context.fancy_error(
//             "`String` type requires a max size argument",
//             vec![Label::primary(name_span, "")],
//             vec!["Example: String<100>".into()],
//         )))),
//         ("Map", Some(args)) => {
//             let diag_voucher = validate_arg_count(context, name, name_span, args, 2, "argument");

//             let key = match args.kind.get(0) {
//                 Some(ast::GenericArg::TypeDesc(type_node)) => match type_desc(context, type_node) {
//                     Ok(Type::Base(base)) => base,
//                     Err(err) => return Some(Err(err)),
//                     _ => {
//                         return Some(Err(TypeError::new(context.error(
//                             "`Map` key must be a primitive type",
//                             type_node.span,
//                             "this can't be used as a Map key",
//                         ))));
//                     }
//                 },
//                 Some(ast::GenericArg::Int(node)) => {
//                     return Some(Err(TypeError::new(context.error(
//                         "`Map` key must be a type",
//                         node.span,
//                         "this should be a type name",
//                     ))));
//                 }
//                 None => return Some(Err(TypeError::new(diag_voucher.unwrap()))),
//             };
//             let value = match args.kind.get(1) {
//                 Some(ast::GenericArg::TypeDesc(type_node)) => match type_desc(context, type_node) {
//                     Ok(typ) => typ,
//                     Err(err) => return Some(Err(err)),
//                 },
//                 Some(ast::GenericArg::Int(node)) => {
//                     return Some(Err(TypeError::new(context.error(
//                         "`Map` value must be a type",
//                         node.span,
//                         "this should be a type name",
//                     ))));
//                 }
//                 None => return Some(Err(TypeError::new(diag_voucher.unwrap()))),
//             };
//             Some(Ok(Type::Map(Map {
//                 key,
//                 value: Box::new(value),
//             })))
//         }
//         ("Map", None) => Some(Err(TypeError::new(context.fancy_error(
//             "`Map` type requires key and value type arguments",
//             vec![Label::primary(name_span, "")],
//             vec!["Example: Map<address, u256>".into()],
//         )))),
//         (_, _) => {
//             let typ = if let Ok(base_type) = Base::from_str(name) {
//                 Type::Base(base_type)
//             } else {
//                 match context.resolve_type(name) {
//                     Some(Ok(typ)) => typ,
//                     Some(Err(err)) => return Some(Err(err)),
//                     None => return None,
//                 }
//             };

//             if let Some(args) = generic_args {
//                 // User-defined types can't be generic yet
//                 context.fancy_error(
//                     &format!("`{}` type is not generic", typ),
//                     vec![Label::primary(args.span, "unexpected type argument list")],
//                     vec![format!("Hint: use `{}`", typ)],
//                 );
//             }
//             Some(Ok(typ))
//         }
//     }
// }

// XXX remove
// fn resolve_type_name_or_err(
//     context: &mut dyn AnalyzerContext,
//     name: &str,
//     name_span: Span,
//     generic_args: Option<&Node<Vec<ast::GenericArg>>>,
// ) -> Result<Type, TypeError> {
//     if let Some(typ) = resolve_type_name(context, name, name_span, generic_args) {
//         typ
//     } else {
//         Err(TypeError::new(context.error(
//             "undefined type",
//             name_span,
//             "this type name has not been defined",
//         )))
//     }
// }

/// Maps a type description node to an enum type.
pub fn type_desc(
    context: &mut dyn AnalyzerContext,
    desc: &Node<ast::TypeDesc>,
) -> Result<Type, TypeError> {
    match &desc.kind {
        ast::TypeDesc::Base { base } => resolve_concrete_type(context, base, desc.span, None),
        ast::TypeDesc::Array { typ, dimension } => {
            if let Type::Base(base) = type_desc(context, typ)? {
                Ok(Type::Array(Array {
                    inner: base,
                    size: *dimension,
                }))
            } else {
                Err(TypeError::new(context.error(
                    "arrays can only hold primitive types",
                    typ.span,
                    "can't be stored in an array",
                )))
            }
        }
        ast::TypeDesc::Generic { base, args } => {
            resolve_concrete_type(context, &base.kind, base.span, Some(args))
        }
        ast::TypeDesc::Tuple { items } => {
            let types = items
                .iter()
                .map(|typ| match FixedSize::try_from(type_desc(context, typ)?) {
                    Ok(typ) => Ok(typ),
                    Err(_) => Err(TypeError::new(context.error(
                        "tuple elements must have fixed size",
                        typ.span,
                        "this can't be stored in a tuple",
                    ))),
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Type::Tuple(Tuple {
                items: Vec1::try_from_vec(types).expect("tuple is empty"),
            }))
        }
        ast::TypeDesc::Unit => Ok(Type::unit()),
    }
}
