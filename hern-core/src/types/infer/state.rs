//! Grouped state carried by the inference engine.
//!
//! `Infer` has several lifetimes of state: session-wide trait knowledge,
//! program-scoped declarations/imports, impl dictionaries, flow stacks, and
//! pending constraints. Grouping fields makes resets and snapshots reflect those
//! type-system roles directly.

use super::*;

#[derive(Debug, Clone, Default)]
pub(super) struct TraitScope {
    /// Active traits for the current program: imported/session traits plus local declarations.
    pub(super) env: HashMap<String, TraitDef>,
    /// Imported/session traits restored at the start of each program.
    pub(super) scoped_env: HashMap<String, TraitDef>,
    /// Active operator-to-trait dispatch map for the current program.
    pub(super) op_trait_map: HashMap<String, String>,
    /// Imported/session operator map restored at the start of each program.
    pub(super) scoped_op_trait_map: HashMap<String, String>,
}

impl TraitScope {
    pub(super) fn insert_trait(
        &mut self,
        trait_def: TraitDef,
        duplicate_span: SourceSpan,
    ) -> Result<(), SpannedTypeError> {
        let mut operator_methods = Vec::new();
        for method in &trait_def.methods {
            if method.fixity.is_none() {
                continue;
            }
            if method.params.len() != 2 {
                return Err(TypeError::TraitMethodArityMismatch {
                    trait_name: trait_def.name.clone(),
                    method: method.name.clone(),
                    expected: 2,
                    got: method.params.len(),
                }
                .at(method.span));
            }
            if let Some(existing) = self.op_trait_map.get(&method.name)
                && existing != &trait_def.name
            {
                return Err(TypeError::DuplicateOperator(method.name.clone()).at(duplicate_span));
            }
            operator_methods.push(method.name.clone());
        }

        let trait_name = trait_def.name.clone();
        self.env.insert(trait_name.clone(), trait_def);
        for operator in operator_methods {
            self.op_trait_map.insert(operator, trait_name.clone());
        }
        Ok(())
    }

    pub(super) fn reset_for_program(&mut self) {
        self.env = self.scoped_env.clone();
        self.op_trait_map = self.scoped_op_trait_map.clone();
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct TypeScope {
    /// Program variant index, rebuilt from seed and local type declarations.
    pub(super) variant_env: VariantEnv,
    /// Program-local aliases, cleared before each inference run.
    pub(super) aliases: HashMap<String, (Vec<String>, Type)>,
    /// Active declared type names: builtins, imports, and current program declarations.
    pub(super) declared: HashSet<String>,
    /// Known constructor arities for builtins and current program type declarations.
    pub(super) constructor_arities: HashMap<String, usize>,
    /// Imported/session type names restored at the start of each program.
    pub(super) scoped_declared: HashSet<String>,
}

impl TypeScope {
    pub(super) fn reset_for_program(&mut self) {
        self.aliases.clear();
        self.declared.clear();
        self.constructor_arities.clear();
        self.declared
            .extend(["string", "bool", "int", "float", "Array", "Iter"].map(str::to_string));
        self.constructor_arities.extend(
            [
                ("string", 0),
                ("bool", 0),
                ("int", 0),
                ("float", 0),
                ("Array", 1),
                ("Iter", 1),
            ]
            .map(|(name, arity)| (name.to_string(), arity)),
        );
        self.declared.extend(self.scoped_declared.iter().cloned());
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct ImportScope {
    pub(super) types: HashMap<String, Ty>,
    pub(super) schemes: HashMap<String, HashMap<String, Scheme>>,
    pub(super) bindings: HashMap<String, String>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct InherentScope {
    pub(super) methods: HashMap<String, HashMap<String, InherentMethodInfo>>,
    pub(super) scoped_methods: HashMap<String, HashMap<String, InherentMethodInfo>>,
    pub(super) record_field_callables: HashMap<String, HashMap<String, Vec<ParamCapability>>>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct ImplScope {
    /// Active concrete impl dictionaries visible during the current program.
    pub(super) active_dicts: HashSet<String>,
    /// Imported/session impl dictionaries restored at the start of each program.
    pub(super) scoped_dicts: HashSet<String>,
    /// Generic impl schemes visible during the current program.
    pub(super) known_schemes: HashMap<String, Scheme>,
}

impl ImplScope {
    pub(super) fn reset_for_program(&mut self) {
        self.active_dicts = self.scoped_dicts.clone();
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct FlowState {
    pub(super) loop_break_tys: Vec<Ty>,
    pub(super) fn_return_tys: Vec<FuncReturn>,
}

impl FlowState {
    pub(super) fn clear(&mut self) {
        self.loop_break_tys.clear();
        self.fn_return_tys.clear();
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct ConstraintState {
    pub(super) pending: Vec<TraitConstraint>,
}

impl ConstraintState {
    pub(super) fn clear(&mut self) {
        self.pending.clear();
    }
}
