use common::ingot::{Ingot, IngotKind};
use hir::{
    analysis::{
        HirAnalysisDb,
        semantic::SemanticInstance,
        ty::{
            trait_def::TraitInstId,
            ty_check::BodyOwner,
            ty_def::{TyBase, TyData, TyId},
        },
    },
    hir_def::{CallableDef, ItemKind, TopLevelMod, scope_graph::ScopeId},
};

pub fn semantic_instance_identity<'db>(
    db: &'db dyn HirAnalysisDb,
    semantic: SemanticInstance<'db>,
) -> String {
    format!(
        "{}${}",
        body_owner_identity(db, semantic.key(db).owner(db)),
        generic_args_identity(db, semantic.key(db).subst(db).generic_args(db))
    )
}

fn body_owner_identity<'db>(db: &'db dyn HirAnalysisDb, owner: BodyOwner<'db>) -> String {
    match owner {
        BodyOwner::Func(func) => {
            let owner_context = semantic_owner_context_identity(db, owner).unwrap_or_default();
            format!("func${}${owner_context}", item_identity(db, func.into()))
        }
        BodyOwner::Const(const_) => format!("const${}", item_identity(db, const_.into())),
        BodyOwner::AnonConstBody { body, expected } => format!(
            "anon_const${}${}",
            module_path_components_for_scope(db, body.scope()).join("$"),
            type_identity(db, expected)
        ),
        BodyOwner::ContractInit { contract } => {
            format!("contract_init${}", item_identity(db, contract.into()))
        }
        BodyOwner::ContractRecvArm {
            contract,
            recv_idx,
            arm_idx,
        } => format!(
            "contract_recv${}${recv_idx}${arm_idx}",
            item_identity(db, contract.into())
        ),
    }
}

pub fn semantic_owner_context_identity<'db>(
    db: &'db dyn HirAnalysisDb,
    owner: BodyOwner<'db>,
) -> Option<String> {
    let BodyOwner::Func(func) = owner else {
        return None;
    };
    if let Some(trait_) = func.containing_trait(db) {
        return Some(format!("trait${}", item_name_component(db, trait_.into())));
    }
    if let Some(impl_trait) = func.containing_impl_trait(db) {
        let trait_identity = impl_trait
            .trait_inst(db)
            .map(|trait_inst| trait_identity(db, trait_inst))
            .unwrap_or_else(|| {
                impl_trait
                    .hir_trait_ref(db)
                    .to_opt()
                    .map(|trait_ref| trait_ref.pretty_print(db))
                    .unwrap_or_else(|| "trait".to_string())
            });
        let impl_identity = format!("{trait_identity}${}", type_identity(db, impl_trait.ty(db)));
        return Some(format!(
            "impl_trait${}",
            stable_identity_hash(&impl_identity)
        ));
    }
    func.containing_impl(db).map(|impl_| {
        format!(
            "impl${}",
            stable_identity_hash(&type_identity(db, impl_.ty(db)))
        )
    })
}

pub fn generic_args_identity<'db>(db: &'db dyn HirAnalysisDb, args: &[TyId<'db>]) -> String {
    args.iter()
        .map(|ty| type_identity(db, *ty))
        .collect::<Vec<_>>()
        .join("$")
}

pub fn type_identity<'db>(db: &'db dyn HirAnalysisDb, ty: TyId<'db>) -> String {
    if matches!(ty.data(db), TyData::TyApp(..)) {
        let base = type_identity(db, ty.base_ty(db));
        let args = ty
            .generic_args(db)
            .iter()
            .map(|arg| type_identity(db, *arg))
            .collect::<Vec<_>>()
            .join("$");
        return format!("app${base}${args}");
    }

    match ty.data(db) {
        TyData::TyBase(base) => match base {
            TyBase::Prim(prim) => format!("prim${prim:?}"),
            TyBase::Adt(adt) => format!("adt${}", item_identity(db, adt.adt_ref(db).as_item())),
            TyBase::Contract(contract) => {
                format!("contract${}", item_identity(db, (*contract).into()))
            }
            TyBase::Func(callable) => match callable {
                CallableDef::Func(func) => format!("func${}", item_identity(db, (*func).into())),
                CallableDef::VariantCtor(variant) => format!(
                    "variant_ctor${}${}",
                    item_identity(db, variant.enum_.into()),
                    variant.name(db).unwrap_or("variant")
                ),
            },
        },
        TyData::TyParam(param) => {
            format!(
                "param${}${}",
                item_identity(db, param.owner.item()),
                param.idx
            )
        }
        TyData::AssocTy(assoc) => format!(
            "assoc${}${}",
            trait_identity(db, assoc.trait_),
            assoc.name.data(db)
        ),
        TyData::QualifiedTy(trait_inst) => format!("qualified${}", trait_identity(db, *trait_inst)),
        TyData::ConstTy(const_ty) => {
            format!(
                "const_ty${}",
                stable_identity_hash(&const_ty.pretty_print_concrete(db))
            )
        }
        TyData::Never => "never".to_string(),
        TyData::TyVar(_) => format!("var${}", stable_identity_hash(ty.pretty_print(db))),
        TyData::Invalid(cause) => {
            format!("invalid${}", stable_identity_hash(&cause.pretty_print(db)))
        }
        TyData::TyApp(..) => unreachable!("TyApp handled before data match"),
    }
}

fn trait_identity<'db>(db: &'db dyn HirAnalysisDb, trait_inst: TraitInstId<'db>) -> String {
    let args = trait_inst
        .args(db)
        .iter()
        .map(|arg| type_identity(db, *arg))
        .collect::<Vec<_>>()
        .join("$");
    let assoc_types = trait_inst
        .assoc_type_bindings(db)
        .iter()
        .map(|(name, ty)| format!("{}${}", name.data(db), type_identity(db, *ty)))
        .collect::<Vec<_>>()
        .join("$");
    format!(
        "{}$args${args}$assoc${assoc_types}",
        item_identity(db, trait_inst.def(db).into())
    )
}

pub fn item_identity<'db>(db: &'db dyn HirAnalysisDb, item: ItemKind<'db>) -> String {
    let top_mod = item.top_mod(db);
    format!(
        "{}${}${}${}",
        ingot_identity_for_top_mod(db, top_mod),
        module_path_components_for_scope(db, item.scope()).join("$"),
        item.kind_name(),
        item_name_component(db, item)
    )
}

fn item_name_component<'db>(db: &'db dyn HirAnalysisDb, item: ItemKind<'db>) -> String {
    item.name(db)
        .map(|name| name.data(db).to_string())
        .unwrap_or_else(|| item.kind_name().replace(' ', "_"))
}

pub fn module_path_components_for_scope<'db>(
    db: &'db dyn HirAnalysisDb,
    scope: ScopeId<'db>,
) -> Vec<String> {
    let mut modules = Vec::new();
    let mut current = scope.parent_module(db);
    while let Some(module_scope) = current {
        match module_scope.item() {
            ItemKind::TopMod(top_mod) => modules.push(top_mod.name(db).data(db).to_string()),
            ItemKind::Mod(module) => modules.push(
                module
                    .name(db)
                    .to_opt()
                    .map(|name| name.data(db).to_string())
                    .unwrap_or_else(|| "mod".to_string()),
            ),
            _ => {}
        }
        current = module_scope.parent_module(db);
    }
    if modules.is_empty() {
        modules.push(scope.top_mod(db).name(db).data(db).to_string());
    }
    modules.reverse();
    modules
}

pub fn ingot_component_for_scope<'db>(db: &'db dyn HirAnalysisDb, scope: ScopeId<'db>) -> String {
    let top_mod = scope.top_mod(db);
    ingot_logical_name(db, top_mod.ingot(db), top_mod)
}

fn ingot_identity_for_top_mod<'db>(
    db: &'db dyn HirAnalysisDb,
    top_mod: TopLevelMod<'db>,
) -> String {
    let ingot = top_mod.ingot(db);
    format!(
        "{:?}${}",
        ingot.kind(db),
        ingot_logical_name(db, ingot, top_mod)
    )
}

fn ingot_logical_name<'db>(
    db: &'db dyn HirAnalysisDb,
    ingot: Ingot<'db>,
    top_mod: TopLevelMod<'db>,
) -> String {
    ingot
        .config(db)
        .and_then(|config| config.metadata.name.map(|name| name.to_string()))
        .unwrap_or_else(|| match ingot.kind(db) {
            IngotKind::Core => "core".to_string(),
            IngotKind::Std => "std".to_string(),
            IngotKind::StandAlone => format!("standalone${}", top_mod.name(db).data(db)),
            IngotKind::Local => format!("local${}", top_mod.name(db).data(db)),
            IngotKind::External => format!("external${}", top_mod.name(db).data(db)),
        })
}

pub fn stable_identity_hash(value: &str) -> String {
    let mut hash = 0xcbf29ce484222325u64;
    for byte in value.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("{hash:016x}")
}
