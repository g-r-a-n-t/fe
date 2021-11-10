use fe_analyzer::namespace::items::{Global, Ingot, Module, ModuleContext, ModuleFileContent};
use fe_analyzer::AnalyzerDb;
use fe_common::diagnostics::Diagnostic;
use fe_common::files::{FileStore, SourceFileId};
use fe_parser::parse_file;
use fe_yulgen::Db;
use indexmap::IndexMap;
#[cfg(feature = "solc-backend")]
use serde_json::Value;
use std::rc::Rc;

/// The artifacts of a compiled module.
pub struct CompiledModule {
    pub src_ast: String,
    pub lowered_ast: String,
    pub contracts: IndexMap<String, CompiledContract>,
}

/// The artifacts of a compiled contract.
pub struct CompiledContract {
    pub json_abi: String,
    pub yul: String,
    #[cfg(feature = "solc-backend")]
    pub bytecode: String,
}

#[derive(Debug)]
pub struct CompileError(pub Vec<Diagnostic>);

/// Compiles the given Fe source code to all targets.
///
/// If `with_bytecode` is set to false, the compiler will skip the final Yul ->
/// Bytecode pass. This is useful when debugging invalid Yul code.
pub fn compile(
    files: &FileStore,
    file_id: SourceFileId,
    _with_bytecode: bool,
    _optimize: bool,
) -> Result<CompiledModule, CompileError> {
    let src = &files.get_file(file_id).expect("missing file").content;

    // parse source
    let mut errors = vec![];

    let (ast, parser_diagnostics) = parse_file(file_id, src).map_err(CompileError)?;
    errors.extend(parser_diagnostics.into_iter());
    let src_ast = format!("{:#?}", &ast);

    let db = Db::default();

    let global = Global::default();
    let global_id = db.intern_global(Rc::new(global));

    let module = Module {
        name: "".to_string(),
        context: ModuleContext::Global(global_id),
        file_content: ModuleFileContent::File { file: file_id },
        ast,
    };
    let module_id = db.intern_module(Rc::new(module));

    match fe_analyzer::analyze_module(&db, module_id) {
        Ok(_) => {}
        Err(diagnostics) => {
            errors.extend(diagnostics.into_iter());
            return Err(CompileError(errors));
        }
    };

    if !errors.is_empty() {
        // There was a non-fatal parser error (eg missing parens in a fn def `fn foo: ...`)
        return Err(CompileError(errors));
    }

    // build abi
    let json_abis = fe_abi::build(&db, module_id).expect("failed to generate abi");

    // lower the AST
    let lowered_module_id = fe_lowering::lower_module(&db, module_id);
    let lowered_ast = format!("{:#?}", &lowered_module_id.ast(&db));

    fe_analyzer::analyze_module(&db, lowered_module_id).expect("failed to analyze lowered AST");

    // compile to yul
    let yul_contracts = fe_yulgen::compile(&db, lowered_module_id);

    // compile to bytecode if required
    #[cfg(feature = "solc-backend")]
    let bytecode_contracts = if _with_bytecode {
        match fe_yulc::compile(yul_contracts.clone(), _optimize) {
            Err(error) => {
                for error in serde_json::from_str::<Value>(&error.0)
                    .expect("unable to deserialize json output")["errors"]
                    .as_array()
                    .expect("errors not an array")
                {
                    eprintln!(
                        "Error: {}",
                        error["formattedMessage"]
                            .as_str()
                            .expect("error value not a string")
                            .replace("\\\n", "\n")
                    )
                }

                panic!("Yul compilation failed with the above errors")
            }
            Ok(contracts) => contracts,
        }
    } else {
        IndexMap::new()
    };

    // combine all of the named contract maps
    let contracts = json_abis
        .keys()
        .map(|name| {
            (
                name.to_owned(),
                CompiledContract {
                    json_abi: json_abis[name].to_owned(),
                    yul: yul_contracts[name].to_owned(),
                    #[cfg(feature = "solc-backend")]
                    bytecode: if _with_bytecode {
                        bytecode_contracts[name].to_owned()
                    } else {
                        "".to_string()
                    },
                },
            )
        })
        .collect::<IndexMap<_, _>>();

    Ok(CompiledModule {
        src_ast,
        lowered_ast,
        contracts,
    })
}

/// Compiles the given Fe source code to all targets.
///
/// If `with_bytecode` is set to false, the compiler will skip the final Yul ->
/// Bytecode pass. This is useful when debugging invalid Yul code.
pub fn compile_ingot(
    files: &FileStore,
    file_ids: &[SourceFileId],
    _with_bytecode: bool,
    _optimize: bool,
) -> Result<CompiledModule, CompileError> {
    // parse source

    let mut errors = vec![];

    let db = Db::default();

    let global = Global::default();
    let global_id = db.intern_global(Rc::new(global));

    let ingot = Ingot {
        name: "".to_string(),
        global: global_id,
        fe_files: file_ids
            .iter()
            .map(|file_id| {
                let file = files.get_file(*file_id).unwrap();
                let ast = parse_file(*file_id, &file.content).unwrap().0;
                (*file_id, (file.to_owned(), ast))
            })
            .collect(),
    };
    let ingot_id = db.intern_ingot(Rc::new(ingot));

    match fe_analyzer::analyze_ingot(&db, ingot_id) {
        Ok(_) => {}
        Err(diagnostics) => {
            errors.extend(diagnostics.into_iter());
            return Err(CompileError(errors));
        }
    };

    if !errors.is_empty() {
        // There was a non-fatal parser error (eg missing parens in a fn def `fn foo: ...`)
        return Err(CompileError(errors));
    }

    let lowered_ingot_id = fe_lowering::lower_ingot(&db, ingot_id);

    fe_analyzer::analyze_ingot(&db, lowered_ingot_id).expect("failed to analyze lowered AST");

    let lowered_module_id = lowered_ingot_id.main_module(&db);

    // TODO: fix this
    // build abi
    let json_abis = fe_abi::build(&db, lowered_module_id).expect("failed to generate abi");
    let src_ast = "".to_string();
    let lowered_ast = "".to_string();

    // compile to yul
    let yul_contracts = fe_yulgen::compile(&db, lowered_module_id);

    // compile to bytecode if required
    #[cfg(feature = "solc-backend")]
    let bytecode_contracts = if _with_bytecode {
        match fe_yulc::compile(yul_contracts.clone(), _optimize) {
            Err(error) => {
                for error in serde_json::from_str::<Value>(&error.0)
                    .expect("unable to deserialize json output")["errors"]
                    .as_array()
                    .expect("errors not an array")
                {
                    eprintln!(
                        "Error: {}",
                        error["formattedMessage"]
                            .as_str()
                            .expect("error value not a string")
                            .replace("\\\n", "\n")
                    )
                }
                panic!("Yul compilation failed with the above errors")
            }
            Ok(contracts) => contracts,
        }
    } else {
        IndexMap::new()
    };

    // combine all of the named contract maps
    let contracts = json_abis
        .keys()
        .map(|name| {
            (
                name.to_owned(),
                CompiledContract {
                    json_abi: json_abis[name].to_owned(),
                    yul: yul_contracts[name].to_owned(),
                    #[cfg(feature = "solc-backend")]
                    bytecode: if _with_bytecode {
                        bytecode_contracts[name].to_owned()
                    } else {
                        "".to_string()
                    },
                },
            )
        })
        .collect::<IndexMap<_, _>>();

    Ok(CompiledModule {
        src_ast,
        lowered_ast,
        contracts,
    })
}
