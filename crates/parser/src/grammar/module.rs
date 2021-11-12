use super::contracts::parse_contract_def;
use super::expressions::parse_expr;
use super::functions::parse_fn_def;
use super::types::{parse_path_tail, parse_struct_def, parse_type_alias, parse_type_desc};
use crate::ast::{ConstantDecl, Module, ModuleStmt, Pragma, Use, UseTree};
use crate::node::{Node, Span};
use crate::{Label, ParseFailed, ParseResult, Parser, TokenKind};

use semver::VersionReq;

/// Parse a [`Module`].
pub fn parse_module(par: &mut Parser) -> ParseResult<Node<Module>> {
    let mut body = vec![];
    loop {
        match par.peek() {
            Some(TokenKind::Newline) => par.expect_newline("module")?,
            Some(TokenKind::Dedent) => {
                par.next()?;
                break;
            }
            None => break,
            Some(_) => {
                let stmt = parse_module_stmt(par)?;
                body.push(stmt);
            }
        }
    }
    let span = Span::zero(par.file_id) + body.first() + body.last();
    Ok(Node::new(Module { body }, span))
}

/// Parse a [`ModuleStmt`].
pub fn parse_module_stmt(par: &mut Parser) -> ParseResult<ModuleStmt> {
    let stmt = match par.peek_or_err()? {
        TokenKind::Pragma => ModuleStmt::Pragma(parse_pragma(par)?),
        TokenKind::Use => ModuleStmt::Use(parse_use(par)?),
        TokenKind::Contract => ModuleStmt::Contract(parse_contract_def(par)?),
        TokenKind::Struct => ModuleStmt::Struct(parse_struct_def(par)?),
        TokenKind::Type => ModuleStmt::TypeAlias(parse_type_alias(par)?),
        TokenKind::Const => ModuleStmt::Constant(Box::new(parse_constant(par)?)),

        // Let these be parse errors for now:
        // TokenKind::Event => todo!("module-level event def"),
        // TokenKind::Name if par.peeked_text() == "from" => parse_from_import(par),
        TokenKind::Pub => {
            let pub_span = par.next()?.span;
            match par.peek_or_err()? {
                TokenKind::Fn | TokenKind::Unsafe => {
                    ModuleStmt::Function(parse_fn_def(par, Some(pub_span))?)
                }
                _ => {
                    let tok = par.next()?;
                    par.unexpected_token_error(
                        tok.span,
                        "failed to parse module",
                        vec!["Note: expected `fn`".into()],
                    );
                    return Err(ParseFailed);
                }
            }
        }
        TokenKind::Fn | TokenKind::Unsafe => ModuleStmt::Function(parse_fn_def(par, None)?),
        _ => {
            let tok = par.next()?;
            par.unexpected_token_error(
                tok.span,
                "failed to parse module",
                vec!["Note: expected import, contract, struct, type, const or event".into()],
            );
            return Err(ParseFailed);
        }
    };
    Ok(stmt)
}

/// Parse a constant, e.g. `const MAGIC_NUMBER: u256 = 4711`.
/// # Panics
/// Panics if the next token isn't `const`.
pub fn parse_constant(par: &mut Parser) -> ParseResult<Node<ConstantDecl>> {
    let const_tok = par.assert(TokenKind::Const);
    let name = par.expect(TokenKind::Name, "failed to parse constant declaration")?;
    par.expect_with_notes(
        TokenKind::Colon,
        "failed to parse constant declaration",
        |_| {
            vec![
                "Note: constant name must be followed by a colon and a type description".into(),
                format!("Example: let `{}: u256 = 1000`", name.text),
            ]
        },
    )?;
    let typ = parse_type_desc(par)?;
    par.expect_with_notes(
        TokenKind::Eq,
        "failed to parse constant declaration",
        |_| {
            vec![
            "Note: the type of a constant must be followed by an equals sign and a value assignment"
                .into(),
                format!(
                    "Example: let `{}: u256 = 1000`",
                    name.text
                ),
        ]
        },
    )?;

    let exp = parse_expr(par)?;

    let span = const_tok.span + exp.span;
    Ok(Node::new(
        ConstantDecl {
            name: name.into(),
            typ,
            value: exp,
        },
        span,
    ))
}

/// Parse a `use` statement.
/// # Panics
/// Panics if the next token isn't `use`.
pub fn parse_use(par: &mut Parser) -> ParseResult<Node<Use>> {
    let use_tok = par.assert(TokenKind::Use);

    let tree = parse_use_tree(par)?;
    let tree_span = tree.span;

    Ok(Node::new(Use { tree }, use_tok.span + tree_span))
}

// /// Parse a `::` delimited path.
// pub fn parse_path(par: &mut Parser) -> ParseResult<Node<Path>> {
//     let mut names = vec![];

//     let name = par.expect_with_notes(TokenKind::Name, "failed to parse path", |_| {
//         vec![
//             "Note: paths must start with a name".into(),
//             "Example: `foo::bar`".into(),
//         ]
//     })?;

//     names.push(Node::new(name.text.to_string(), name.span));

//     loop {
//         if par.peek() == Some(TokenKind::ColonColon) {
//             let delim_tok = par.next()?;

//             if par.peek() == Some(TokenKind::Name) {
//                 let name = par.next()?;

//                 names.push(Node::new(name.text.to_string(), name.span));
//             } else {
//                 let span =
//                     names.first().expect("`names` should not be empty").span + delim_tok.span;

//                 return Ok(Node::new(
//                     Path {
//                         segments,
//                         trailing_delim: true,
//                     },
//                     span,
//                 ));
//             }
//         } else {
//             let span = names.first().expect("`names` should not be empty").span
//                 + names.last().expect("").span;

//             return Ok(Node::new(
//                 Path {
//                     names,
//                     trailing_delim: false,
//                 },
//                 span,
//             ));
//         }
//     }
// }

/// Parse a `use` tree.
pub fn parse_use_tree(par: &mut Parser) -> ParseResult<Node<UseTree>> {
    let (path, path_span, trailing_delim) = {
        let path_head =
            par.expect_with_notes(TokenKind::Name, "failed to parse `use` statement", |_| {
                vec![
                    "Note: `use` paths must start with a name".into(),
                    "Example: `use foo::bar`".into(),
                ]
            })?;
        parse_path_tail(par, path_head.into())
    };

    if trailing_delim.is_some() {
        match par.peek() {
            Some(TokenKind::BraceOpen) => {
                par.next()?;

                let mut children = vec![];
                let close_brace_span;

                loop {
                    children.push(parse_use_tree(par)?);
                    let tok = par.next()?;
                    match tok.kind {
                        TokenKind::Comma => {
                            continue;
                        }
                        TokenKind::BraceClose => {
                            close_brace_span = tok.span;
                            break;
                        }
                        _ => {
                            par.unexpected_token_error(
                                tok.span,
                                "failed to parse `use` tree",
                                vec!["Note: expected a `,` or `}` token".to_string()],
                            );
                            return Err(ParseFailed);
                        }
                    }
                }

                Ok(Node::new(
                    UseTree::Nested {
                        prefix: path,
                        children,
                    },
                    close_brace_span,
                ))
            }
            Some(TokenKind::Star) => {
                par.next()?;
                Ok(Node::new(UseTree::Glob { prefix: path }, path_span))
            }
            _ => {
                let tok = par.next()?;
                par.unexpected_token_error(
                    tok.span,
                    "failed to parse `use` tree",
                    vec!["Note: expected a `*`, `{` or name token".to_string()],
                );
                Err(ParseFailed)
            }
        }
    } else if par.peek() == Some(TokenKind::As) {
        par.next()?;

        let rename_tok = par.expect(TokenKind::Name, "failed to parse `use` tree")?;
        let rename = Some(Node::new(rename_tok.text.to_string(), rename_tok.span));

        Ok(Node::new(
            UseTree::Simple { path, rename },
            path_span + rename_tok.span,
        ))
    } else {
        Ok(Node::new(UseTree::Simple { path, rename: None }, path_span))
    }
}

/// Parse a `pragma <version-requirement>` statement.
pub fn parse_pragma(par: &mut Parser) -> ParseResult<Node<Pragma>> {
    let tok = par.assert(TokenKind::Pragma);
    assert_eq!(tok.text, "pragma");

    let mut version_string = String::new();
    let mut tokens = vec![];
    loop {
        match par.peek() {
            Some(TokenKind::Newline) => break,
            None => break,
            _ => {
                let tok = par.next()?;
                version_string.push_str(tok.text);
                tokens.push(tok);
            }
        }
    }

    let version_requirement_span = match (tokens.first(), tokens.last()) {
        (Some(first), Some(last)) => first.span + last.span,
        _ => {
            par.error(
                tok.span,
                "failed to parse pragma statement: missing version requirement",
            );
            return Err(ParseFailed);
        }
    };

    match VersionReq::parse(&version_string) {
        Ok(_) => Ok(Node::new(
            Pragma {
                version_requirement: Node::new(version_string, version_requirement_span),
            },
            tok.span + version_requirement_span,
        )),
        Err(err) => {
            par.fancy_error(
                format!("failed to parse pragma statement: {}", err),
                vec![Label::primary(
                    version_requirement_span,
                    "Invalid version requirement",
                )],
                vec!["Example: `^0.5.0`".into()],
            );
            Err(ParseFailed)
        }
    }
}
