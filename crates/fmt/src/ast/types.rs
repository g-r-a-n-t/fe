//! Formatting for types, paths, generics, and type-related constructs.

use pretty::{DocAllocator, DocBuilder, RcAllocator};

use crate::RewriteContext;
use parser::ast::{
    self, GenericArgKind, GenericArgsOwner, GenericParamKind, TypeKind, prelude::AstNode,
};
use parser::syntax_kind::SyntaxKind;
use parser::syntax_node::NodeOrToken;

/// Type alias for the document builder type used throughout formatting.
pub type Doc<'a> = DocBuilder<'a, RcAllocator, ()>;

/// Extension trait for converting AST nodes to pretty documents.
pub trait ToDoc {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a>;
}

/// Helper to intersperse documents with a separator.
pub fn intersperse<'a>(
    alloc: &'a RcAllocator,
    docs: impl IntoIterator<Item = Doc<'a>>,
    sep: Doc<'a>,
) -> Doc<'a> {
    alloc.intersperse(docs, sep)
}

/// Creates a Rust-style block format for delimited lists.
///
/// When flat (non-spaced): `(item1, item2)` (e.g., for parens/brackets)
/// When flat (spaced): `{ item1, item2 }` (e.g., for braces)
/// When broken:
/// ```text
/// open
///     item1,
///     item2,
/// close
/// ```
///
/// The `trailing_comma` parameter controls whether a trailing comma is added
/// when the list is broken across multiple lines.
pub fn block_list<'a>(
    ctx: &'a RewriteContext<'a>,
    open: &'a str,
    close: &'a str,
    items: Vec<Doc<'a>>,
    indent: isize,
    trailing_comma: bool,
) -> Doc<'a> {
    block_list_inner(ctx, open, close, items, indent, trailing_comma, false)
}

/// Like `block_list`, but adds spaces inside delimiters when rendered flat.
/// Use this for brace-delimited lists like `{ x, y }`.
pub fn block_list_spaced<'a>(
    ctx: &'a RewriteContext<'a>,
    open: &'a str,
    close: &'a str,
    items: Vec<Doc<'a>>,
    indent: isize,
    trailing_comma: bool,
) -> Doc<'a> {
    block_list_inner(ctx, open, close, items, indent, trailing_comma, true)
}

pub fn has_comment_tokens(syntax: &parser::SyntaxNode) -> bool {
    syntax.children_with_tokens().any(|child| {
        matches!(
            child,
            NodeOrToken::Token(t) if matches!(t.kind(), SyntaxKind::Comment | SyntaxKind::DocComment)
        )
    })
}

pub fn block_list_with_comments<'a, T: ToDoc>(
    ctx: &'a RewriteContext<'a>,
    syntax: &parser::SyntaxNode,
    open: &'a str,
    close: &'a str,
    cast_fn: impl Fn(parser::SyntaxNode) -> Option<T>,
    indent: isize,
    trailing_comma: bool,
) -> Doc<'a> {
    let alloc = &ctx.alloc;

    #[derive(Clone)]
    enum Entry<'a> {
        Element(Doc<'a>),
        Comment(String),
    }

    struct EntryWithSpacing<'a> {
        entry: Entry<'a>,
        blank_line_before: bool,
    }

    let mut entries: Vec<EntryWithSpacing<'a>> = Vec::new();
    let mut pending_newlines = 0usize;

    for child in syntax.children_with_tokens() {
        match child {
            NodeOrToken::Node(node) => {
                let Some(elem) = cast_fn(node) else {
                    continue;
                };
                entries.push(EntryWithSpacing {
                    entry: Entry::Element(elem.to_doc(ctx)),
                    blank_line_before: pending_newlines >= 2,
                });
                pending_newlines = 0;
            }
            NodeOrToken::Token(token) => match token.kind() {
                SyntaxKind::Newline => {
                    let text = ctx.snippet(token.text_range());
                    pending_newlines += text.chars().filter(|c| *c == '\n').count();
                }
                SyntaxKind::WhiteSpace => {}
                SyntaxKind::Comment | SyntaxKind::DocComment => {
                    entries.push(EntryWithSpacing {
                        entry: Entry::Comment(
                            ctx.snippet(token.text_range()).trim_end().to_string(),
                        ),
                        blank_line_before: pending_newlines >= 2,
                    });
                    pending_newlines = 0;
                }
                _ => {}
            },
        }
    }

    if entries.is_empty() {
        return alloc.text(format!("{open}{close}"));
    }

    let last_element_idx = entries
        .iter()
        .rposition(|e| matches!(e.entry, Entry::Element(_)));

    let mut inner = alloc.nil();
    for (idx, entry) in entries.into_iter().enumerate() {
        let newlines_to_add = if entry.blank_line_before { 2 } else { 1 };
        for _ in 0..newlines_to_add {
            inner = inner.append(alloc.hardline());
        }

        match entry.entry {
            Entry::Element(doc) => {
                let is_last_element = last_element_idx == Some(idx);
                let elem_doc = if trailing_comma || !is_last_element {
                    doc.append(alloc.text(","))
                } else {
                    doc
                };
                inner = inner.append(elem_doc);
            }
            Entry::Comment(text) => {
                inner = inner.append(alloc.text(text));
            }
        }
    }

    alloc
        .text(open)
        .append(inner.nest(indent))
        .append(alloc.hardline())
        .append(alloc.text(close))
}

fn block_list_inner<'a>(
    ctx: &'a RewriteContext<'a>,
    open: &'a str,
    close: &'a str,
    items: Vec<Doc<'a>>,
    indent: isize,
    trailing_comma: bool,
    spaced: bool,
) -> Doc<'a> {
    let alloc = &ctx.alloc;

    if items.is_empty() {
        return alloc.text(format!("{}{}", open, close));
    }

    let sep = alloc.text(",").append(alloc.line());
    let inner = intersperse(alloc, items, sep);

    let trailing = if trailing_comma {
        alloc.text(",").flat_alt(alloc.nil())
    } else {
        alloc.nil()
    };

    // For spaced variant, use line() which renders as space when flat
    // For non-spaced variant, use line_() which renders as empty when flat
    let break_token = if spaced { alloc.line() } else { alloc.line_() };

    alloc
        .text(open)
        .append(
            break_token
                .clone()
                .append(inner)
                .append(trailing)
                .nest(indent),
        )
        .append(break_token)
        .append(alloc.text(close))
        .group()
}

impl ToDoc for ast::GenericParamList {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let indent = ctx.config.indent_width as isize;
        if has_comment_tokens(self.syntax()) {
            block_list_with_comments(
                ctx,
                self.syntax(),
                "<",
                ">",
                ast::GenericParam::cast,
                indent,
                true,
            )
        } else {
            let params: Vec<_> = self.into_iter().map(|p| p.to_doc(ctx)).collect();
            block_list(ctx, "<", ">", params, indent, true)
        }
    }
}

impl ToDoc for ast::GenericParam {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        match self.kind() {
            GenericParamKind::Type(ty_param) => ty_param.to_doc(ctx),
            GenericParamKind::Const(const_param) => const_param.to_doc(ctx),
        }
    }
}

impl ToDoc for ast::TypeGenericParam {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        let name = self
            .name()
            .map(|n| alloc.text(ctx.token(&n).to_string()))
            .unwrap_or_else(|| alloc.nil());

        let bounds = self
            .bounds()
            .map(|b| b.to_doc(ctx))
            .unwrap_or_else(|| alloc.nil());

        let default = self
            .default_ty()
            .map(|ty| alloc.text(" = ").append(ty.to_doc(ctx)))
            .unwrap_or_else(|| alloc.nil());

        name.append(bounds).append(default)
    }
}

impl ToDoc for ast::ConstGenericParam {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        let name = self
            .name()
            .map(|n| alloc.text(ctx.token(&n).to_string()))
            .unwrap_or_else(|| alloc.nil());

        let ty = self
            .ty()
            .map(|ty| alloc.text(": ").append(ty.to_doc(ctx)))
            .unwrap_or_else(|| alloc.nil());

        alloc.text("const ").append(name).append(ty)
    }
}

impl ToDoc for ast::WhereClause {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        let predicates: Vec<_> = self.into_iter().map(|pred| pred.to_doc(ctx)).collect();

        if predicates.is_empty() {
            return alloc.nil();
        }

        let sep = alloc.text(",").append(alloc.line());
        let inner = intersperse(alloc, predicates, sep);

        inner.group()
    }
}

impl ToDoc for ast::WherePredicate {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        let ty = match self.ty() {
            Some(t) => t.to_doc(ctx),
            None => return alloc.nil(),
        };

        if let Some(bounds) = self.bounds() {
            ty.append(bounds.to_doc(ctx))
        } else {
            ty
        }
    }
}

impl ToDoc for ast::TypeBoundList {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        let bounds: Vec<_> = self.into_iter().map(|bound| bound.to_doc(ctx)).collect();

        if bounds.is_empty() {
            return alloc.nil();
        }

        let sep = alloc.text(" + ");
        alloc.text(": ").append(intersperse(alloc, bounds, sep))
    }
}

impl ToDoc for ast::TypeBound {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        if let Some(trait_bound) = self.trait_bound() {
            trait_bound.to_doc(ctx)
        } else if let Some(kind_bound) = self.kind_bound() {
            alloc.text(ctx.snippet_trimmed(&kind_bound))
        } else {
            alloc.nil()
        }
    }
}

impl ToDoc for ast::TraitRef {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        match self.path() {
            Some(p) => p.to_doc(ctx),
            None => ctx.alloc.nil(),
        }
    }
}

impl ToDoc for ast::SuperTraitList {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        let traits: Vec<_> = self.into_iter().map(|t| t.to_doc(ctx)).collect();

        if traits.is_empty() {
            return alloc.nil();
        }

        let sep = alloc.text(" + ");
        alloc.text(": ").append(intersperse(alloc, traits, sep))
    }
}

impl ToDoc for ast::Type {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        match self.kind() {
            TypeKind::Ptr(ptr) => ptr.to_doc(ctx),
            TypeKind::Path(path) => path.to_doc(ctx),
            TypeKind::Tuple(tuple) => tuple.to_doc(ctx),
            TypeKind::Array(array) => array.to_doc(ctx),
            TypeKind::Never(never) => never.to_doc(ctx),
        }
    }
}

impl ToDoc for ast::PtrType {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        match self.inner() {
            Some(inner) => alloc.text("*").append(inner.to_doc(ctx)),
            None => alloc.text("*"),
        }
    }
}

impl ToDoc for ast::PathType {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        match self.path() {
            Some(p) => p.to_doc(ctx),
            None => ctx.alloc.nil(),
        }
    }
}

impl ToDoc for ast::Path {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        let segments: Vec<_> = self.segments().map(|seg| seg.to_doc(ctx)).collect();

        let sep = alloc.text("::");
        intersperse(alloc, segments, sep)
    }
}

impl ToDoc for ast::PathSegment {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;
        let mut doc = alloc.nil();

        if let Some(kind) = self.kind() {
            match kind {
                ast::PathSegmentKind::QualifiedType(q) => {
                    doc = q.to_doc(ctx);
                }
                _ => {
                    if let Some(ident) = self.ident() {
                        doc = alloc.text(ctx.snippet(ident.text_range()).trim().to_string());
                    }
                }
            }
        }

        if let Some(args) = self.generic_args() {
            doc = doc.append(args.to_doc(ctx));
        }

        doc
    }
}

impl ToDoc for ast::QualifiedType {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        let ty = match self.ty() {
            Some(t) => t.to_doc(ctx),
            None => return alloc.nil(),
        };
        let trait_path = match self.trait_qualifier() {
            Some(p) => p.to_doc(ctx),
            None => return alloc.nil(),
        };

        alloc
            .text("<")
            .append(ty)
            .append(alloc.text(" as "))
            .append(trait_path)
            .append(alloc.text(">"))
    }
}

impl ToDoc for ast::GenericArgList {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let indent = ctx.config.indent_width as isize;
        if has_comment_tokens(self.syntax()) {
            block_list_with_comments(
                ctx,
                self.syntax(),
                "<",
                ">",
                ast::GenericArg::cast,
                indent,
                true,
            )
        } else {
            let args: Vec<_> = self.into_iter().map(|a| a.to_doc(ctx)).collect();
            block_list(ctx, "<", ">", args, indent, true)
        }
    }
}

impl ToDoc for ast::GenericArg {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        match self.kind() {
            GenericArgKind::Type(ty_arg) => ty_arg.to_doc(ctx),
            GenericArgKind::Const(const_arg) => const_arg.to_doc(ctx),
            GenericArgKind::AssocType(assoc_arg) => assoc_arg.to_doc(ctx),
        }
    }
}

impl ToDoc for ast::TypeGenericArg {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        match self.ty() {
            Some(t) => t.to_doc(ctx),
            None => ctx.alloc.nil(),
        }
    }
}

impl ToDoc for ast::ConstGenericArg {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        match self.expr() {
            Some(e) => e.to_doc(ctx),
            None => ctx.alloc.nil(),
        }
    }
}

impl ToDoc for ast::AssocTypeGenericArg {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        let name = match self.name() {
            Some(n) => ctx.snippet(n.text_range()).trim().to_string(),
            None => return alloc.nil(),
        };
        let ty = match self.ty() {
            Some(t) => t.to_doc(ctx),
            None => return alloc.nil(),
        };

        alloc.text(name).append(alloc.text(" = ")).append(ty)
    }
}

impl ToDoc for ast::TupleType {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let indent = ctx.config.indent_width as isize;
        if has_comment_tokens(self.syntax()) {
            block_list_with_comments(ctx, self.syntax(), "(", ")", ast::Type::cast, indent, true)
        } else {
            let elems: Vec<_> = self.elem_tys().map(|e| e.to_doc(ctx)).collect();
            block_list(ctx, "(", ")", elems, indent, true)
        }
    }
}

impl ToDoc for ast::ArrayType {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        let alloc = &ctx.alloc;

        let elem_ty = match self.elem_ty() {
            Some(t) => t.to_doc(ctx),
            None => return alloc.nil(),
        };
        let len = match self.len() {
            Some(l) => l.to_doc(ctx),
            None => return alloc.nil(),
        };

        alloc
            .text("[")
            .append(elem_ty)
            .append(alloc.text("; "))
            .append(len)
            .append(alloc.text("]"))
    }
}

impl ToDoc for ast::NeverType {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        ctx.alloc.text("!")
    }
}

// Forward declaration for expr::ToDoc - dispatches to specific expression types
impl ToDoc for ast::Expr {
    fn to_doc<'a>(&self, ctx: &'a RewriteContext<'a>) -> Doc<'a> {
        use parser::ast::ExprKind;
        match self.kind() {
            ExprKind::Lit(lit) => lit.to_doc(ctx),
            ExprKind::Block(block) => block.to_doc(ctx),
            ExprKind::Bin(bin) => bin.to_doc(ctx),
            ExprKind::Un(un) => un.to_doc(ctx),
            ExprKind::Cast(cast) => cast.to_doc(ctx),
            ExprKind::Call(call) => call.to_doc(ctx),
            ExprKind::MethodCall(method) => method.to_doc(ctx),
            ExprKind::Path(path) => path.to_doc(ctx),
            ExprKind::RecordInit(record) => record.to_doc(ctx),
            ExprKind::Field(field) => field.to_doc(ctx),
            ExprKind::Index(index) => index.to_doc(ctx),
            ExprKind::Tuple(tuple) => tuple.to_doc(ctx),
            ExprKind::Array(array) => array.to_doc(ctx),
            ExprKind::ArrayRep(array_rep) => array_rep.to_doc(ctx),
            ExprKind::If(if_expr) => if_expr.to_doc(ctx),
            ExprKind::Match(match_expr) => match_expr.to_doc(ctx),
            ExprKind::With(with_expr) => with_expr.to_doc(ctx),
            ExprKind::Paren(paren) => paren.to_doc(ctx),
            ExprKind::Assign(assign) => assign.to_doc(ctx),
            ExprKind::AugAssign(aug_assign) => aug_assign.to_doc(ctx),
        }
    }
}
