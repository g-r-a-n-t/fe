//! Module-level Yul emission helpers (functions + code regions).

use driver::DriverDataBase;
use hir::hir_def::TopLevelMod;
use mir::analysis::{
    ContractRegion, ContractRegionKind, build_call_graph, build_contract_graph, reachable_functions,
};
use mir::{MirFunction, lower_module};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{collections::VecDeque, sync::Arc};

use crate::yul::doc::{YulDoc, render_docs};
use crate::yul::errors::YulError;

use super::{EmitModuleError, function::FunctionEmitter};

/// Emits Yul for every function in the lowered MIR module.
///
/// * `db` - Driver database used to query compiler facts.
/// * `top_mod` - Root module to lower.
///
/// Returns a single Yul string containing all lowered functions followed by any
/// auto-generated code regions, or [`EmitModuleError`] if MIR lowering or Yul
/// emission fails.
pub fn emit_module_yul(
    db: &DriverDataBase,
    top_mod: TopLevelMod<'_>,
) -> Result<String, EmitModuleError> {
    let module = lower_module(db, top_mod).map_err(EmitModuleError::MirLower)?;

    let contract_graph = build_contract_graph(&module.functions);

    let mut code_regions = FxHashMap::default();
    for (name, entry) in &contract_graph.contracts {
        if let Some(init) = &entry.init_symbol {
            code_regions.insert(init.clone(), name.clone());
        }
        if let Some(runtime) = &entry.deployed_symbol {
            code_regions.insert(runtime.clone(), format!("{name}_deployed"));
        }
    }
    let code_region_roots = collect_code_region_roots(&module.functions);
    for root in &code_region_roots {
        if code_regions.contains_key(root) {
            continue;
        }
        code_regions
            .entry(root.clone())
            .or_insert_with(|| format!("code_region_{}", sanitize_symbol(root)));
    }
    let code_regions = Arc::new(code_regions);

    // Emit Yul docs for each function
    let mut function_docs: Vec<Vec<YulDoc>> = Vec::with_capacity(module.functions.len());
    for func in module.functions.iter() {
        let emitter =
            FunctionEmitter::new(db, func, &code_regions).map_err(EmitModuleError::Yul)?;
        let docs = emitter.emit_doc().map_err(EmitModuleError::Yul)?;
        function_docs.push(docs);
    }

    // Index function docs by symbol for region assembly.
    let mut docs_by_symbol = FxHashMap::default();
    for (idx, func) in module.functions.iter().enumerate() {
        docs_by_symbol.insert(
            func.symbol_name.clone(),
            FunctionDocInfo {
                docs: function_docs[idx].clone(),
            },
        );
    }

    let mut contract_deps: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
    let mut referenced_contracts = FxHashSet::default();
    for (from_region, deps) in &contract_graph.region_deps {
        for dep in deps {
            if dep.contract_name != from_region.contract_name {
                referenced_contracts.insert(dep.contract_name.clone());
                contract_deps
                    .entry(from_region.contract_name.clone())
                    .or_default()
                    .insert(dep.contract_name.clone());
            }
        }
    }

    let mut root_contracts: Vec<_> = contract_graph
        .contracts
        .keys()
        .filter(|name| !referenced_contracts.contains(*name))
        .cloned()
        .collect();
    root_contracts.sort();

    // Ensure the contract dependency graph is rooted; otherwise we'd silently omit contracts or
    // fall back to emitting raw functions (which breaks `dataoffset/datasize` scoping).
    if !contract_graph.contracts.is_empty() {
        let mut visited = FxHashSet::default();
        let mut queue = VecDeque::new();
        for name in &root_contracts {
            queue.push_back(name.clone());
        }
        while let Some(name) = queue.pop_front() {
            if !visited.insert(name.clone()) {
                continue;
            }
            if let Some(deps) = contract_deps.get(&name) {
                for dep in deps {
                    queue.push_back(dep.clone());
                }
            }
        }
        if visited.len() != contract_graph.contracts.len() {
            let mut missing: Vec<_> = contract_graph
                .contracts
                .keys()
                .filter(|name| !visited.contains(*name))
                .cloned()
                .collect();
            missing.sort();
            return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
                "contract region graph is not rooted (cycle likely); unreachable contracts: {}",
                missing.join(", ")
            ))));
        }
    }

    let mut docs = Vec::new();
    for name in root_contracts {
        let mut stack = Vec::new();
        docs.push(
            emit_contract_init_object(&name, &contract_graph, &docs_by_symbol, &mut stack)
                .map_err(EmitModuleError::Yul)?,
        );
    }

    // Free-function code regions not tied to contract entrypoints.
    let call_graph = build_call_graph(&module.functions);
    for root in code_region_roots {
        if contract_graph.symbol_to_region.contains_key(&root) {
            continue;
        }
        let Some(label) = code_regions.get(&root) else {
            continue;
        };
        let reachable = reachable_functions(&call_graph, &root);
        let mut region_docs = Vec::new();
        let mut symbols: Vec<_> = reachable.into_iter().collect();
        symbols.sort();
        for symbol in symbols {
            if let Some(info) = docs_by_symbol.get(&symbol) {
                region_docs.extend(info.docs.clone());
            }
        }
        docs.push(YulDoc::block(
            format!("object \"{label}\" "),
            vec![YulDoc::block("code ", region_docs)],
        ));
    }

    // If nothing was emitted (no regions), fall back to top-level functions.
    if docs.is_empty() {
        for func_docs in function_docs {
            docs.extend(func_docs);
        }
    }

    let mut lines = Vec::new();
    render_docs(&docs, 0, &mut lines);
    Ok(join_lines(lines))
}

/// Joins rendered lines while trimming trailing whitespace-only entries.
///
/// * `lines` - Vector of rendered Yul lines.
///
/// Returns the normalized Yul output string.
fn join_lines(mut lines: Vec<String>) -> String {
    while lines.last().is_some_and(|line| line.is_empty()) {
        lines.pop();
    }
    lines.join("\n")
}

/// Collects all function symbols referenced by `code_region` intrinsics and all contract
/// entrypoints.
fn collect_code_region_roots(functions: &[MirFunction<'_>]) -> Vec<String> {
    let mut roots = FxHashSet::default();
    for func in functions {
        if func.contract_function.is_some() {
            roots.insert(func.symbol_name.clone());
        }
        for block in &func.body.blocks {
            for inst in &block.insts {
                if let mir::MirInst::Assign {
                    rvalue: mir::Rvalue::Intrinsic { op, args },
                    ..
                } = inst
                    && matches!(
                        *op,
                        mir::ir::IntrinsicOp::CodeRegionOffset
                            | mir::ir::IntrinsicOp::CodeRegionLen
                    )
                    && args.len() == 1
                    && let Some(arg) = args.first().copied()
                    && let mir::ValueOrigin::FuncItem(target) = &func.body.value(arg).origin
                    && let Some(symbol) = &target.symbol
                {
                    roots.insert(symbol.clone());
                }
            }
        }
    }
    let mut out: Vec<_> = roots.into_iter().collect();
    out.sort();
    out
}

/// Replace any non-alphanumeric characters with `_` so the label is a valid Yul identifier.
fn sanitize_symbol(component: &str) -> String {
    component
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
        .collect()
}

struct FunctionDocInfo {
    docs: Vec<YulDoc>,
}

fn emit_contract_init_object(
    name: &str,
    graph: &mir::analysis::ContractGraph,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
    stack: &mut Vec<ContractRegion>,
) -> Result<YulDoc, YulError> {
    let entry = graph
        .contracts
        .get(name)
        .ok_or_else(|| YulError::Unsupported(format!("missing contract info for `{name}`")))?;
    let region = ContractRegion {
        contract_name: name.to_string(),
        kind: ContractRegionKind::Init,
    };
    push_region(stack, &region)?;

    let mut components = Vec::new();

    let mut init_docs = Vec::new();
    if let Some(symbol) = &entry.init_symbol {
        init_docs.extend(reachable_docs_for_region(graph, &region, docs_by_symbol));
        init_docs.push(YulDoc::line(format!("{symbol}()")));
    }
    components.push(YulDoc::block("code ", init_docs));

    // Always emit the deployed object (if present) for the contract itself.
    if entry.deployed_symbol.is_some() {
        components.push(YulDoc::line(String::new()));
        components.push(emit_contract_deployed_object(
            name,
            graph,
            docs_by_symbol,
            stack,
        )?);
    }

    // Emit direct region dependencies as children of the init object. These must be direct
    // children to satisfy Yul `dataoffset/datasize` scoping rules.
    let deps = graph.region_deps.get(&region).cloned().unwrap_or_default();
    let mut deps: Vec<_> = deps
        .into_iter()
        .filter(|dep| {
            !(dep.contract_name == name && matches!(dep.kind, ContractRegionKind::Deployed))
        })
        .collect();
    deps.sort();
    for dep in deps {
        components.push(emit_region_object(&dep, graph, docs_by_symbol, stack)?);
    }

    pop_region(stack, &region);
    Ok(YulDoc::block(format!("object \"{name}\" "), components))
}

fn emit_contract_deployed_object(
    contract_name: &str,
    graph: &mir::analysis::ContractGraph,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
    stack: &mut Vec<ContractRegion>,
) -> Result<YulDoc, YulError> {
    let entry = graph.contracts.get(contract_name).ok_or_else(|| {
        YulError::Unsupported(format!("missing contract info for `{contract_name}`"))
    })?;
    let Some(symbol) = &entry.deployed_symbol else {
        return Err(YulError::Unsupported(format!(
            "missing deployed entrypoint for `{contract_name}`"
        )));
    };

    let region = ContractRegion {
        contract_name: contract_name.to_string(),
        kind: ContractRegionKind::Deployed,
    };
    push_region(stack, &region)?;

    let mut runtime_docs = Vec::new();
    runtime_docs.extend(reachable_docs_for_region(graph, &region, docs_by_symbol));
    runtime_docs.push(YulDoc::line(format!("{symbol}()")));
    runtime_docs.push(YulDoc::line("return(0, 0)"));

    let mut components = vec![YulDoc::block("code ", runtime_docs)];

    let deps = graph.region_deps.get(&region).cloned().unwrap_or_default();
    let mut deps: Vec<_> = deps.into_iter().collect();
    deps.sort();
    for dep in deps {
        components.push(emit_region_object(&dep, graph, docs_by_symbol, stack)?);
    }

    pop_region(stack, &region);
    Ok(YulDoc::block(
        format!("object \"{contract_name}_deployed\" "),
        components,
    ))
}

fn emit_region_object(
    region: &ContractRegion,
    graph: &mir::analysis::ContractGraph,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
    stack: &mut Vec<ContractRegion>,
) -> Result<YulDoc, YulError> {
    match region.kind {
        ContractRegionKind::Init => {
            emit_contract_init_object(&region.contract_name, graph, docs_by_symbol, stack)
        }
        ContractRegionKind::Deployed => {
            emit_contract_deployed_object(&region.contract_name, graph, docs_by_symbol, stack)
        }
    }
}

fn reachable_docs_for_region(
    graph: &mir::analysis::ContractGraph,
    region: &ContractRegion,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
) -> Vec<YulDoc> {
    let mut docs = Vec::new();
    let Some(reachable) = graph.region_reachable.get(region) else {
        return docs;
    };
    let mut symbols: Vec<_> = reachable.iter().cloned().collect();
    symbols.sort();
    for symbol in symbols {
        if let Some(info) = docs_by_symbol.get(&symbol) {
            docs.extend(info.docs.clone());
        }
    }
    docs
}

fn push_region(stack: &mut Vec<ContractRegion>, region: &ContractRegion) -> Result<(), YulError> {
    if stack.iter().any(|r| r == region) {
        let mut cycle = stack
            .iter()
            .map(|r| format!("{}::{:?}", r.contract_name, r.kind))
            .collect::<Vec<_>>();
        cycle.push(format!("{}::{:?}", region.contract_name, region.kind));
        return Err(YulError::Unsupported(format!(
            "cycle detected in contract region graph: {}",
            cycle.join(" -> ")
        )));
    }
    stack.push(region.clone());
    Ok(())
}

fn pop_region(stack: &mut Vec<ContractRegion>, region: &ContractRegion) {
    let popped = stack.pop();
    debug_assert_eq!(popped.as_ref(), Some(region));
}
