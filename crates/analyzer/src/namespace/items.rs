use crate::builtins;
use crate::context;
use crate::errors::{self, TypeError};
use crate::impl_intern_key;
use crate::namespace::types::{self, GenericType};
use crate::traversal::pragma::check_pragma_version;
use crate::AnalyzerDb;
use fe_common::diagnostics::Diagnostic;
use fe_common::files::{SourceFile, SourceFileId};
use fe_parser::ast;
use fe_parser::ast::Expr;
use fe_parser::node::{Node, Span};
use indexmap::indexmap;
use indexmap::IndexMap;
use std::collections::BTreeMap;
use std::path::Path;
use std::rc::Rc;

/// A named item. This does not include things inside of
/// a function body.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Item {
    Ingot(IngotId),
    Module(ModuleId),
    // Constant // TODO: when `const` is implemented
    Type(TypeDef),
    // GenericType probably shouldn't be a separate category.
    // Any of the items inside TypeDef (struct, alias, etc)
    // could be optionally generic.
    GenericType(GenericType),
    // Events aren't normal types; they *could* be moved into
    // TypeDef, but it would have consequences.
    Event(EventId),
    Function(FunctionId),
    Constant(ModuleConstantId),
    // Needed until we can represent keccak256 as a FunctionId.
    // We can't represent keccak256's arg type yet.
    BuiltinFunction(builtins::GlobalFunction),

    // This should go away soon. The globals (block, msg, etc) will be replaced
    // with a context struct that'll appear in the fn parameter list.
    // `self` should just be removed from here and handled as a special parameter.
    Object(builtins::GlobalObject),
}

impl Item {
    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        match self {
            Item::Type(id) => id.name(db),
            Item::GenericType(id) => id.name().to_string(),
            Item::Event(id) => id.name(db),
            Item::Function(id) => id.name(db),
            Item::BuiltinFunction(id) => id.as_ref().to_string(),
            Item::Object(id) => id.as_ref().to_string(),
            Item::Constant(id) => id.name(db),
            Item::Ingot(id) => id.name(db),
            Item::Module(id) => id.name(db),
        }
    }

    pub fn name_span(&self, db: &dyn AnalyzerDb) -> Option<Span> {
        match self {
            Item::Type(id) => id.name_span(db),
            Item::GenericType(_) => None,
            Item::Event(id) => Some(id.name_span(db)),
            Item::Function(id) => Some(id.name_span(db)),
            Item::BuiltinFunction(_) => None,
            Item::Object(_) => None,
            Item::Constant(id) => Some(id.name_span(db)),
            Item::Ingot(_) => None,
            Item::Module(_) => None,
        }
    }

    pub fn is_builtin(&self) -> bool {
        match self {
            Item::Type(TypeDef::Primitive(_)) => true,
            Item::Type(_) => false,
            Item::GenericType(_) => true,
            Item::Event(_) => false,
            Item::Function(_) => false,
            Item::BuiltinFunction(_) => true,
            Item::Object(_) => true,
            Item::Constant(_) => false,
            Item::Ingot(_) => false,
            Item::Module(_) => false,
        }
    }

    pub fn item_kind_display_name(&self) -> &'static str {
        match self {
            Item::Type(_) => "type",
            Item::GenericType(_) => "type",
            Item::Event(_) => "event",
            Item::Function(_) => "function",
            Item::BuiltinFunction(_) => "function",
            Item::Object(_) => "object",
            Item::Constant(_) => "constant",
            Item::Ingot(_) => "ingot",
            Item::Module(_) => "module",
        }
    }

    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        match self {
            Item::Type(id) => id.sink_diagnostics(db, sink),
            Item::GenericType(_) => {}
            Item::Event(id) => id.sink_diagnostics(db, sink),
            Item::Function(id) => id.sink_diagnostics(db, sink),
            Item::BuiltinFunction(_) => {}
            Item::Object(_) => {}
            Item::Constant(id) => id.sink_diagnostics(db, sink),
            Item::Ingot(id) => id.sink_diagnostics(db, sink),
            Item::Module(id) => id.sink_diagnostics(db, sink),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Default)]
pub struct Global {
    ingots: BTreeMap<String, IngotId>,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct GlobalId(pub(crate) u32);
impl_intern_key!(GlobalId);
impl GlobalId {}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Ingot {
    pub name: String,
    // pub version: String,
    pub global: GlobalId,
    // `BTreeMap` implements `Hash`, which is required for an ID.
    pub fe_files: BTreeMap<SourceFileId, (SourceFile, ast::Module)>,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct IngotId(pub(crate) u32);
impl_intern_key!(IngotId);
impl IngotId {
    pub fn data(&self, db: &dyn AnalyzerDb) -> Rc<Ingot> {
        db.lookup_intern_ingot(*self)
    }

    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        self.data(db).name.clone()
    }

    pub fn main_module(&self, db: &dyn AnalyzerDb) -> ModuleId {
        *self
            .all_modules(db)
            .iter()
            // TODO: finding by name is not valid
            .find(|module_id| module_id.name(db) == "main")
            .unwrap()
    }

    pub fn diagnostics(&self, db: &dyn AnalyzerDb) -> Vec<Diagnostic> {
        let mut diagnostics = vec![];
        self.sink_diagnostics(db, &mut diagnostics);
        diagnostics
    }

    pub fn all_modules(&self, db: &dyn AnalyzerDb) -> Rc<Vec<ModuleId>> {
        db.ingot_all_modules(*self)
    }

    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        let modules = self.all_modules(db);

        for module in modules.iter() {
            module.sink_diagnostics(db, sink)
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum ModuleFileContent {
    Dir {
        // file: SourceFileId,
        // dir_files: Vec<SourceFileId>
        dir_path: String,
    },
    File {
        file: SourceFileId,
    },
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum ModuleContext {
    Ingot(IngotId),
    Global(GlobalId),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Module {
    pub name: String,
    pub context: ModuleContext,
    pub file_content: ModuleFileContent,
    pub ast: ast::Module,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct ModuleId(pub(crate) u32);
impl_intern_key!(ModuleId);
impl ModuleId {
    pub fn data(&self, db: &dyn AnalyzerDb) -> Rc<Module> {
        db.lookup_intern_module(*self)
    }

    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        self.data(db).name.clone()
    }

    pub fn file_content(&self, db: &dyn AnalyzerDb) -> ModuleFileContent {
        self.data(db).file_content.clone()
    }

    pub fn ingot_path(&self, db: &dyn AnalyzerDb) -> String {
        match self.context(db) {
            ModuleContext::Ingot(ingot) => match self.file_content(db) {
                ModuleFileContent::Dir { dir_path } => dir_path.clone(),
                ModuleFileContent::File { file } => ingot.data(db).fe_files[&file].0.name.clone(),
            },
            ModuleContext::Global(_) => panic!("cant do this"),
        }
    }

    pub fn has_dir(&self, db: &dyn AnalyzerDb) -> bool {
        match self.file_content(db) {
            ModuleFileContent::Dir { .. } => true,
            ModuleFileContent::File { .. } => false,
        }
    }

    pub fn ast(&self, db: &dyn AnalyzerDb) -> ast::Module {
        self.data(db).ast.clone()
    }

    pub fn context(&self, db: &dyn AnalyzerDb) -> ModuleContext {
        self.data(db).context.clone()
    }

    /// Returns a map of the named items in the module
    pub fn items(&self, db: &dyn AnalyzerDb) -> Rc<IndexMap<String, Item>> {
        db.module_item_map(*self).value
    }

    /// Includes duplicate names
    pub fn all_items(&self, db: &dyn AnalyzerDb) -> Rc<Vec<Item>> {
        db.module_all_items(*self)
    }

    pub fn used_items(&self, db: &dyn AnalyzerDb) -> Rc<IndexMap<String, Item>> {
        db.module_used_item_map(*self)
    }

    pub fn resolve_name(&self, db: &dyn AnalyzerDb, name: &str) -> Option<Item> {
        self.items(db)
            .get(name)
            .copied()
            .or_else(|| self.used_items(db).get(name).copied())
    }

    pub fn resolve_sub_path(&self, db: &dyn AnalyzerDb, path: &[String]) -> Option<Item> {
        let mut curr_module = *self;

        for name in path.iter().take(path.len() - 1) {
            // TODO: add module not found diagnostic message
            curr_module = *curr_module.sub_modules(db).get(name).unwrap()
        }

        // TODO: add item not found diagnostic message
        curr_module
            .items(db)
            .get(path.last().expect("path is empty"))
            .or_else(|| panic!("{:?}", path.last()))
            .copied()
    }

    /// All contracts, including duplicates
    pub fn all_contracts(&self, db: &dyn AnalyzerDb) -> Rc<Vec<ContractId>> {
        db.module_contracts(*self)
    }

    /// All structs, including duplicates
    pub fn all_structs(&self, db: &dyn AnalyzerDb) -> Rc<Vec<StructId>> {
        db.module_structs(*self)
    }

    pub fn diagnostics(&self, db: &dyn AnalyzerDb) -> Vec<Diagnostic> {
        let mut diagnostics = vec![];
        self.sink_diagnostics(db, &mut diagnostics);
        diagnostics
    }

    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        let ast::Module { body } = &self.data(db).ast;
        for stmt in body {
            match stmt {
                ast::ModuleStmt::Pragma(inner) => {
                    if let Some(diag) = check_pragma_version(inner) {
                        sink.push(&diag)
                    }
                }
                _ => {} // everything else is a type def, handled below.
            }
        }

        // duplicate item name errors
        sink.push_all(db.module_item_map(*self).diagnostics.iter());

        // errors for each item
        self.all_items(db)
            .iter()
            .for_each(|id| id.sink_diagnostics(db, sink));
    }

    pub fn parent_module(&self, db: &dyn AnalyzerDb) -> Option<ModuleId> {
        match self.context(db) {
            ModuleContext::Ingot(ingot) => {
                let all_modules = ingot.all_modules(db);

                for module_id in all_modules.iter() {
                    if module_id
                        .sub_modules(db)
                        .values()
                        .collect::<Vec<_>>()
                        .contains(&self)
                    {
                        return Some(*module_id);
                    }
                }

                None
            }
            ModuleContext::Global(_) => None,
        }
    }

    pub fn adjacent_modules(&self, db: &dyn AnalyzerDb) -> Rc<IndexMap<String, ModuleId>> {
        if let Some(parent) = self.parent_module(db) {
            parent.sub_modules(db)
        } else {
            Rc::new(indexmap! {})
        }
    }

    pub fn sub_modules(&self, db: &dyn AnalyzerDb) -> Rc<IndexMap<String, ModuleId>> {
        match self.context(db) {
            ModuleContext::Ingot(ingot) => {
                let all_modules = ingot.all_modules(db);

                match self.file_content(db) {
                    ModuleFileContent::Dir { dir_path } => {
                        // TODO: clean this up
                        let sub_modules = all_modules
                            .iter()
                            .filter(|module_id| {
                                Path::new(&module_id.ingot_path(db)).parent().unwrap()
                                    == Path::new(&dir_path)
                            })
                            .map(|module_id| (module_id.name(db), *module_id))
                            .collect::<IndexMap<_, _>>();
                        Rc::new(sub_modules)
                    }
                    ModuleFileContent::File { .. } => Rc::new(indexmap! {}),
                }
            }
            ModuleContext::Global(_) => Rc::new(indexmap! {}),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct ModuleConstant {
    pub ast: Node<ast::ConstantDecl>,
    pub module: ModuleId,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct ModuleConstantId(pub(crate) u32);
impl_intern_key!(ModuleConstantId);

impl ModuleConstantId {
    pub fn data(&self, db: &dyn AnalyzerDb) -> Rc<ModuleConstant> {
        db.lookup_intern_module_const(*self)
    }
    pub fn span(&self, db: &dyn AnalyzerDb) -> Span {
        self.data(db).ast.span
    }
    pub fn typ(&self, db: &dyn AnalyzerDb) -> Result<types::Type, TypeError> {
        db.module_constant_type(*self).value
    }

    pub fn is_base_type(&self, db: &dyn AnalyzerDb) -> bool {
        matches!(self.typ(db), Ok(types::Type::Base(_)))
    }

    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        self.data(db).ast.kind.name.kind.clone()
    }

    pub fn name_span(&self, db: &dyn AnalyzerDb) -> Span {
        self.data(db).ast.kind.name.span
    }

    pub fn value(&self, db: &dyn AnalyzerDb) -> fe_parser::ast::Expr {
        self.data(db).ast.kind.value.kind.clone()
    }

    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        db.module_constant_type(*self)
            .diagnostics
            .iter()
            .for_each(|d| sink.push(d));

        if !matches!(
            self.value(db),
            Expr::Bool(_) | Expr::Num(_) | Expr::Str(_) | Expr::Unit
        ) {
            sink.push(&errors::error(
                "non-literal expressions not yet supported for constants",
                self.data(db).ast.kind.value.span,
                "not a literal",
            ))
        }
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum TypeDef {
    Alias(TypeAliasId),
    Struct(StructId),
    Contract(ContractId),
    Primitive(types::Base),
}
impl TypeDef {
    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        match self {
            TypeDef::Alias(id) => id.name(db),
            TypeDef::Struct(id) => id.name(db),
            TypeDef::Contract(id) => id.name(db),
            TypeDef::Primitive(typ) => typ.to_string(),
        }
    }

    pub fn name_span(&self, db: &dyn AnalyzerDb) -> Option<Span> {
        match self {
            TypeDef::Alias(id) => Some(id.name_span(db)),
            TypeDef::Struct(id) => Some(id.name_span(db)),
            TypeDef::Contract(id) => Some(id.name_span(db)),
            TypeDef::Primitive(_) => None,
        }
    }

    pub fn typ(&self, db: &dyn AnalyzerDb) -> Result<types::Type, TypeError> {
        match self {
            TypeDef::Alias(id) => id.typ(db),
            TypeDef::Struct(id) => Ok(types::Type::Struct(types::Struct {
                id: *id,
                name: id.name(db),
                field_count: id.fields(db).len(), // for the EvmSized trait
            })),
            TypeDef::Contract(id) => Ok(types::Type::Contract(types::Contract {
                id: *id,
                name: id.name(db),
            })),
            TypeDef::Primitive(base) => Ok(types::Type::Base(*base)),
        }
    }

    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        match self {
            TypeDef::Alias(id) => id.sink_diagnostics(db, sink),
            TypeDef::Struct(id) => id.sink_diagnostics(db, sink),
            TypeDef::Contract(id) => id.sink_diagnostics(db, sink),
            TypeDef::Primitive(_) => {}
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct TypeAlias {
    pub ast: Node<ast::TypeAlias>,
    pub module: ModuleId,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct TypeAliasId(pub(crate) u32);
impl_intern_key!(TypeAliasId);

impl TypeAliasId {
    pub fn data(&self, db: &dyn AnalyzerDb) -> Rc<TypeAlias> {
        db.lookup_intern_type_alias(*self)
    }
    pub fn span(&self, db: &dyn AnalyzerDb) -> Span {
        self.data(db).ast.span
    }
    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        self.data(db).ast.name().to_string()
    }
    pub fn name_span(&self, db: &dyn AnalyzerDb) -> Span {
        self.data(db).ast.kind.name.span
    }
    pub fn typ(&self, db: &dyn AnalyzerDb) -> Result<types::Type, TypeError> {
        db.type_alias_type(*self).value
    }
    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        db.type_alias_type(*self)
            .diagnostics
            .iter()
            .for_each(|d| sink.push(d))
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Contract {
    pub name: String,
    pub ast: Node<ast::Contract>,
    pub module: ModuleId,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct ContractId(pub(crate) u32);
impl_intern_key!(ContractId);
impl ContractId {
    pub fn data(&self, db: &dyn AnalyzerDb) -> Rc<Contract> {
        db.lookup_intern_contract(*self)
    }
    pub fn span(&self, db: &dyn AnalyzerDb) -> Span {
        self.data(db).ast.span
    }
    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        self.data(db).ast.name().to_string()
    }
    pub fn name_span(&self, db: &dyn AnalyzerDb) -> Span {
        self.data(db).ast.kind.name.span
    }

    pub fn module(&self, db: &dyn AnalyzerDb) -> ModuleId {
        self.data(db).module
    }

    pub fn fields(&self, db: &dyn AnalyzerDb) -> Rc<IndexMap<String, ContractFieldId>> {
        db.contract_field_map(*self).value
    }

    pub fn field_type(
        &self,
        db: &dyn AnalyzerDb,
        name: &str,
    ) -> Option<(Result<types::Type, TypeError>, usize)> {
        let fields = db.contract_field_map(*self).value;
        let (index, _, field) = fields.get_full(name)?;
        Some((field.typ(db), index))
    }

    pub fn resolve_name(&self, db: &dyn AnalyzerDb, name: &str) -> Option<Item> {
        self.function(db, name)
            .filter(|f| !f.takes_self(db))
            .map(Item::Function)
            .or_else(|| self.event(db, name).map(Item::Event))
            .or_else(|| self.module(db).resolve_name(db, name))
    }

    pub fn init_function(&self, db: &dyn AnalyzerDb) -> Option<FunctionId> {
        db.contract_init_function(*self).value
    }

    /// User functions, public and not. Excludes `__init__`.
    pub fn functions(&self, db: &dyn AnalyzerDb) -> Rc<IndexMap<String, FunctionId>> {
        db.contract_function_map(*self).value
    }

    /// Lookup a function by name. Searches all user functions, private or not. Excludes init function.
    pub fn function(&self, db: &dyn AnalyzerDb, name: &str) -> Option<FunctionId> {
        self.functions(db).get(name).copied()
    }

    /// Excludes `__init__`.
    pub fn public_functions(&self, db: &dyn AnalyzerDb) -> Rc<IndexMap<String, FunctionId>> {
        db.contract_public_function_map(*self)
    }

    /// Get a function that takes self by its name.
    pub fn self_function(&self, db: &dyn AnalyzerDb, name: &str) -> Option<FunctionId> {
        self.function(db, name).filter(|f| f.takes_self(db))
    }

    /// Lookup an event by name.
    pub fn event(&self, db: &dyn AnalyzerDb, name: &str) -> Option<EventId> {
        self.events(db).get(name).copied()
    }

    /// A map of events defined within the contract.
    pub fn events(&self, db: &dyn AnalyzerDb) -> Rc<IndexMap<String, EventId>> {
        db.contract_event_map(*self).value
    }

    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        // fields
        db.contract_field_map(*self).sink_diagnostics(sink);
        db.contract_all_fields(*self)
            .iter()
            .for_each(|field| field.sink_diagnostics(db, sink));

        // events
        db.contract_event_map(*self).sink_diagnostics(sink);
        db.contract_all_events(*self)
            .iter()
            .for_each(|event| event.sink_diagnostics(db, sink));

        // functions
        db.contract_init_function(*self).sink_diagnostics(sink);
        db.contract_function_map(*self).sink_diagnostics(sink);
        db.contract_all_functions(*self)
            .iter()
            .for_each(|id| id.sink_diagnostics(db, sink));
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct ContractField {
    pub ast: Node<ast::Field>,
    pub parent: ContractId,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct ContractFieldId(pub(crate) u32);
impl_intern_key!(ContractFieldId);
impl ContractFieldId {
    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        self.data(db).ast.name().to_string()
    }
    pub fn data(&self, db: &dyn AnalyzerDb) -> Rc<ContractField> {
        db.lookup_intern_contract_field(*self)
    }
    pub fn typ(&self, db: &dyn AnalyzerDb) -> Result<types::Type, TypeError> {
        db.contract_field_type(*self).value
    }
    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        sink.push_all(db.contract_field_type(*self).diagnostics.iter())
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Function {
    pub ast: Node<ast::Function>,
    pub module: ModuleId,
    pub parent: Option<Class>,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct FunctionId(pub(crate) u32);
impl_intern_key!(FunctionId);
impl FunctionId {
    pub fn data(&self, db: &dyn AnalyzerDb) -> Rc<Function> {
        db.lookup_intern_function(*self)
    }
    pub fn span(&self, db: &dyn AnalyzerDb) -> Span {
        self.data(db).ast.span
    }
    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        self.data(db).ast.name().to_string()
    }
    pub fn name_span(&self, db: &dyn AnalyzerDb) -> Span {
        self.data(db).ast.kind.name.span
    }

    pub fn parent(&self, db: &dyn AnalyzerDb) -> Option<Class> {
        self.data(db).parent
    }

    pub fn module(&self, db: &dyn AnalyzerDb) -> ModuleId {
        self.data(db).module
    }

    pub fn takes_self(&self, db: &dyn AnalyzerDb) -> bool {
        self.signature(db).self_decl.is_some()
    }
    pub fn self_span(&self, db: &dyn AnalyzerDb) -> Option<Span> {
        if self.takes_self(db) {
            self.data(db)
                .ast
                .kind
                .args
                .iter()
                .find_map(|arg| matches!(arg.kind, ast::FunctionArg::Zelf).then(|| arg.span))
        } else {
            None
        }
    }

    pub fn is_public(&self, db: &dyn AnalyzerDb) -> bool {
        self.pub_span(db).is_some()
    }
    pub fn pub_span(&self, db: &dyn AnalyzerDb) -> Option<Span> {
        self.data(db).ast.kind.pub_
    }
    pub fn unsafe_span(&self, db: &dyn AnalyzerDb) -> Option<Span> {
        self.data(db).ast.kind.unsafe_
    }
    pub fn signature(&self, db: &dyn AnalyzerDb) -> Rc<types::FunctionSignature> {
        db.function_signature(*self).value
    }
    pub fn body(&self, db: &dyn AnalyzerDb) -> Rc<context::FunctionBody> {
        db.function_body(*self).value
    }
    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        sink.push_all(db.function_signature(*self).diagnostics.iter());
        sink.push_all(db.function_body(*self).diagnostics.iter());
    }
}

/// A `Class` is an item that can have member functions.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Class {
    Contract(ContractId),
    Struct(StructId),
}
impl Class {
    pub fn function(&self, db: &dyn AnalyzerDb, name: &str) -> Option<FunctionId> {
        match self {
            Class::Contract(id) => id.function(db, name),
            Class::Struct(id) => id.function(db, name),
        }
    }
    pub fn self_function(&self, db: &dyn AnalyzerDb, name: &str) -> Option<FunctionId> {
        let fun = self.function(db, name)?;
        fun.takes_self(db).then(|| fun)
    }

    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        match self {
            Class::Contract(inner) => inner.name(db),
            Class::Struct(inner) => inner.name(db),
        }
    }
    pub fn kind(&self) -> &str {
        match self {
            Class::Contract(_) => "contract",
            Class::Struct(_) => "struct",
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum MemberFunction {
    BuiltIn(builtins::ValueMethod),
    Function(FunctionId),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Struct {
    pub ast: Node<ast::Struct>,
    pub module: ModuleId,
}

#[derive(Default, Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct StructId(pub(crate) u32);
impl_intern_key!(StructId);
impl StructId {
    pub fn data(&self, db: &dyn AnalyzerDb) -> Rc<Struct> {
        db.lookup_intern_struct(*self)
    }
    pub fn span(&self, db: &dyn AnalyzerDb) -> Span {
        self.data(db).ast.span
    }
    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        self.data(db).ast.name().to_string()
    }
    pub fn name_span(&self, db: &dyn AnalyzerDb) -> Span {
        self.data(db).ast.kind.name.span
    }
    pub fn module(&self, db: &dyn AnalyzerDb) -> ModuleId {
        self.data(db).module
    }
    pub fn typ(&self, db: &dyn AnalyzerDb) -> Rc<types::Struct> {
        db.struct_type(*self)
    }

    pub fn field(&self, db: &dyn AnalyzerDb, name: &str) -> Option<StructFieldId> {
        self.fields(db).get(name).copied()
    }
    pub fn field_type(
        &self,
        db: &dyn AnalyzerDb,
        name: &str,
    ) -> Option<Result<types::FixedSize, TypeError>> {
        Some(self.field(db, name)?.typ(db))
    }

    pub fn fields(&self, db: &dyn AnalyzerDb) -> Rc<IndexMap<String, StructFieldId>> {
        db.struct_field_map(*self).value
    }
    pub fn functions(&self, db: &dyn AnalyzerDb) -> Rc<IndexMap<String, FunctionId>> {
        db.struct_function_map(*self).value
    }
    pub fn function(&self, db: &dyn AnalyzerDb, name: &str) -> Option<FunctionId> {
        self.functions(db).get(name).copied()
    }
    pub fn self_function(&self, db: &dyn AnalyzerDb, name: &str) -> Option<FunctionId> {
        self.function(db, name).filter(|f| f.takes_self(db))
    }
    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        sink.push_all(db.struct_field_map(*self).diagnostics.iter());
        db.struct_all_fields(*self)
            .iter()
            .for_each(|id| id.sink_diagnostics(db, sink));

        db.struct_all_functions(*self)
            .iter()
            .for_each(|id| id.sink_diagnostics(db, sink));
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct StructField {
    pub ast: Node<ast::Field>,
    pub parent: StructId,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct StructFieldId(pub(crate) u32);
impl_intern_key!(StructFieldId);
impl StructFieldId {
    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        self.data(db).ast.name().to_string()
    }
    pub fn data(&self, db: &dyn AnalyzerDb) -> Rc<StructField> {
        db.lookup_intern_struct_field(*self)
    }
    pub fn typ(&self, db: &dyn AnalyzerDb) -> Result<types::FixedSize, TypeError> {
        db.struct_field_type(*self).value
    }
    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        db.struct_field_type(*self).sink_diagnostics(sink)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Event {
    pub ast: Node<ast::Event>,
    pub contract: ContractId,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct EventId(pub(crate) u32);
impl_intern_key!(EventId);

impl EventId {
    pub fn name(&self, db: &dyn AnalyzerDb) -> String {
        self.data(db).ast.name().to_string()
    }
    pub fn name_span(&self, db: &dyn AnalyzerDb) -> Span {
        self.data(db).ast.kind.name.span
    }
    pub fn data(&self, db: &dyn AnalyzerDb) -> Rc<Event> {
        db.lookup_intern_event(*self)
    }
    pub fn typ(&self, db: &dyn AnalyzerDb) -> Rc<types::Event> {
        db.event_type(*self).value
    }
    pub fn module(&self, db: &dyn AnalyzerDb) -> ModuleId {
        self.data(db).contract.module(db)
    }
    pub fn sink_diagnostics(&self, db: &dyn AnalyzerDb, sink: &mut impl DiagnosticSink) {
        sink.push_all(db.event_type(*self).diagnostics.iter());
    }
}

pub trait DiagnosticSink {
    fn push(&mut self, diag: &Diagnostic);
    fn push_all<'a>(&mut self, iter: impl Iterator<Item = &'a Diagnostic>) {
        iter.for_each(|diag| self.push(diag))
    }
}

impl DiagnosticSink for Vec<Diagnostic> {
    fn push(&mut self, diag: &Diagnostic) {
        self.push(diag.clone())
    }
    fn push_all<'a>(&mut self, iter: impl Iterator<Item = &'a Diagnostic>) {
        self.extend(iter.cloned())
    }
}
