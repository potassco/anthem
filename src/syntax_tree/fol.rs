use {
    crate::{
        convenience::apply::Apply as _,
        formatting::fol::default::Format,
        parsing::fol::pest::{
            AnnotatedFormulaParser, AtomParser, AtomicFormulaParser, BinaryConnectiveParser,
            BinaryOperatorParser, ComparisonParser, DirectionParser, FormulaParser,
            FunctionConstantParser, GeneralTermParser, GuardParser, IntegerTermParser,
            PlaceholderDeclarationParser, PredicateParser, QuantificationParser, QuantifierParser,
            RelationParser, RoleParser, SortParser, SpecificationParser, SymbolicTermParser,
            TheoryParser, UnaryConnectiveParser, UnaryOperatorParser, UserGuideEntryParser,
            UserGuideParser, VariableParser,
        },
        simplifying::fol::ht::join_nested_quantifiers,
        syntax_tree::{impl_node, Node},
        verifying::problem,
    },
    clap::ValueEnum,
    derive_more::derive::IntoIterator,
    indexmap::{IndexMap, IndexSet},
    std::hash::Hash,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryOperator {
    Negative,
}

impl_node!(UnaryOperator, Format, UnaryOperatorParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
}

impl_node!(BinaryOperator, Format, BinaryOperatorParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum IntegerTerm {
    Numeral(isize),
    FunctionConstant(String),
    Variable(String),
    UnaryOperation {
        op: UnaryOperator,
        arg: Box<IntegerTerm>,
    },
    BinaryOperation {
        op: BinaryOperator,
        lhs: Box<IntegerTerm>,
        rhs: Box<IntegerTerm>,
    },
}

impl_node!(IntegerTerm, Format, IntegerTermParser);

impl IntegerTerm {
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            IntegerTerm::Numeral(_) | IntegerTerm::FunctionConstant(_) => IndexSet::new(),
            IntegerTerm::Variable(v) => IndexSet::from([Variable {
                name: v.to_string(),
                sort: Sort::Integer,
            }]),
            IntegerTerm::UnaryOperation { arg: t, .. } => t.variables(),
            IntegerTerm::BinaryOperation { lhs, rhs, .. } => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars
            }
        }
    }

    pub fn function_constants(&self) -> IndexSet<FunctionConstant> {
        match &self {
            IntegerTerm::FunctionConstant(c) => IndexSet::from([FunctionConstant {
                name: c.clone(),
                sort: Sort::Integer,
            }]),
            IntegerTerm::Numeral(_) | IntegerTerm::Variable(_) => IndexSet::new(),
            IntegerTerm::UnaryOperation { arg: t, .. } => t.function_constants(),
            IntegerTerm::BinaryOperation { lhs, rhs, .. } => {
                let mut constants = lhs.function_constants();
                constants.extend(rhs.function_constants());
                constants
            }
        }
    }

    pub fn substitute(self, var: Variable, term: IntegerTerm) -> Self {
        match self {
            IntegerTerm::Variable(s) if var.name == s && var.sort == Sort::Integer => term,
            IntegerTerm::Numeral(_)
            | IntegerTerm::FunctionConstant(_)
            | IntegerTerm::Variable(_) => self,
            IntegerTerm::UnaryOperation { op, arg } => IntegerTerm::UnaryOperation {
                op,
                arg: arg.substitute(var, term).into(),
            },
            IntegerTerm::BinaryOperation { op, lhs, rhs } => IntegerTerm::BinaryOperation {
                op,
                lhs: lhs.substitute(var.clone(), term.clone()).into(),
                rhs: rhs.substitute(var, term).into(),
            },
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SymbolicTerm {
    Symbol(String),
    FunctionConstant(String),
    Variable(String),
}

impl_node!(SymbolicTerm, Format, SymbolicTermParser);

impl SymbolicTerm {
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            SymbolicTerm::Symbol(_) | SymbolicTerm::FunctionConstant(_) => IndexSet::new(),
            SymbolicTerm::Variable(v) => IndexSet::from([Variable {
                name: v.to_string(),
                sort: Sort::Symbol,
            }]),
        }
    }

    pub fn symbols(&self) -> IndexSet<String> {
        match &self {
            SymbolicTerm::Symbol(s) => IndexSet::from([s.clone()]),
            SymbolicTerm::FunctionConstant(_) | SymbolicTerm::Variable(_) => IndexSet::new(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<FunctionConstant> {
        match &self {
            SymbolicTerm::FunctionConstant(c) => IndexSet::from([FunctionConstant {
                name: c.clone(),
                sort: Sort::Symbol,
            }]),
            SymbolicTerm::Symbol(_) | SymbolicTerm::Variable(_) => IndexSet::new(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum GeneralTerm {
    Infimum,
    Supremum,
    FunctionConstant(String),
    Variable(String),
    IntegerTerm(IntegerTerm),
    SymbolicTerm(SymbolicTerm),
}

impl_node!(GeneralTerm, Format, GeneralTermParser);

impl GeneralTerm {
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            GeneralTerm::Infimum | GeneralTerm::Supremum | GeneralTerm::FunctionConstant(_) => {
                IndexSet::new()
            }
            GeneralTerm::Variable(v) => IndexSet::from([Variable {
                name: v.to_string(),
                sort: Sort::General,
            }]),
            GeneralTerm::IntegerTerm(t) => t.variables(),
            GeneralTerm::SymbolicTerm(t) => t.variables(),
        }
    }

    pub fn symbols(&self) -> IndexSet<String> {
        match &self {
            GeneralTerm::SymbolicTerm(t) => t.symbols(),
            _ => IndexSet::new(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<FunctionConstant> {
        match &self {
            GeneralTerm::FunctionConstant(c) => IndexSet::from([FunctionConstant {
                name: c.clone(),
                sort: Sort::General,
            }]),
            GeneralTerm::IntegerTerm(t) => t.function_constants(),
            GeneralTerm::SymbolicTerm(t) => t.function_constants(),
            GeneralTerm::Infimum | GeneralTerm::Supremum | GeneralTerm::Variable(_) => {
                IndexSet::new()
            }
        }
    }

    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        match self {
            GeneralTerm::Variable(s) if var.name == s && var.sort == Sort::General => term,
            GeneralTerm::IntegerTerm(t) if var.sort == Sort::Integer => match term {
                GeneralTerm::IntegerTerm(term) => GeneralTerm::IntegerTerm(t.substitute(var, term)),
                _ => panic!(
                    "cannot substitute general term `{term}` for the integer variable `{var}`"
                ),
            },
            t => t,
        }
    }

    fn rename_conflicting_symbols(self, possible_conflicts: &IndexSet<Predicate>) -> Self {
        match self {
            GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol(s)) => {
                let predicate = Predicate {
                    symbol: s.clone(),
                    arity: 0,
                };
                // TODO: increment new name while conflicts exist
                if possible_conflicts.contains(&predicate) {
                    GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol(format!("{s}__s")))
                } else {
                    GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol(s))
                }
            }
            x => x,
        }
    }

    fn replace_placeholders(self, mapping: &IndexMap<String, FunctionConstant>) -> Self {
        match self {
            GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol(s)) => {
                if let Some(fc) = mapping.get(&s) {
                    match fc.sort {
                        Sort::General => GeneralTerm::FunctionConstant(s),
                        Sort::Integer => GeneralTerm::IntegerTerm(IntegerTerm::FunctionConstant(s)),
                        Sort::Symbol => {
                            GeneralTerm::SymbolicTerm(SymbolicTerm::FunctionConstant(s))
                        }
                    }
                } else {
                    GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol(s))
                }
            }
            x => x,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Predicate {
    pub symbol: String,
    pub arity: usize,
}

impl_node!(Predicate, Format, PredicateParser);

impl Predicate {
    pub fn to_formula(self) -> Formula {
        Formula::AtomicFormula(AtomicFormula::Atom(Atom {
            predicate_symbol: self.symbol,
            terms: (1..=self.arity)
                .map(|i| GeneralTerm::Variable(format!("X{i}")))
                .collect(),
        }))
    }
}

impl From<crate::syntax_tree::asp::Predicate> for Predicate {
    fn from(value: crate::syntax_tree::asp::Predicate) -> Self {
        Predicate {
            symbol: value.symbol,
            arity: value.arity,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Atom {
    pub predicate_symbol: String,
    pub terms: Vec<GeneralTerm>,
}

impl Atom {
    pub fn predicate(&self) -> Predicate {
        Predicate {
            symbol: self.predicate_symbol.clone(),
            arity: self.terms.len(),
        }
    }

    fn rename_conflicting_symbols(self, possible_conflicts: &IndexSet<Predicate>) -> Self {
        Atom {
            predicate_symbol: self.predicate_symbol,
            terms: self
                .terms
                .into_iter()
                .map(|t| t.rename_conflicting_symbols(possible_conflicts))
                .collect(),
        }
    }

    pub fn replace_placeholders(self, mapping: &IndexMap<String, FunctionConstant>) -> Self {
        Atom {
            predicate_symbol: self.predicate_symbol,
            terms: self
                .terms
                .into_iter()
                .map(|t| t.replace_placeholders(mapping))
                .collect(),
        }
    }
}

impl_node!(Atom, Format, AtomParser);

impl Atom {
    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        let predicate_symbol = self.predicate_symbol;

        let mut terms = Vec::new();
        for t in self.terms {
            terms.push(t.substitute(var.clone(), term.clone()))
        }

        Atom {
            predicate_symbol,
            terms,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Relation {
    Equal,
    NotEqual,
    Greater,
    Less,
    GreaterEqual,
    LessEqual,
}

impl_node!(Relation, Format, RelationParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Guard {
    pub relation: Relation,
    pub term: GeneralTerm,
}

impl_node!(Guard, Format, GuardParser);

impl Guard {
    pub fn variables(&self) -> IndexSet<Variable> {
        self.term.variables()
    }

    pub fn symbols(&self) -> IndexSet<String> {
        self.term.symbols()
    }

    pub fn function_constants(&self) -> IndexSet<FunctionConstant> {
        self.term.function_constants()
    }

    pub fn replace_placeholders(self, mapping: &IndexMap<String, FunctionConstant>) -> Self {
        Guard {
            relation: self.relation,
            term: self.term.replace_placeholders(mapping),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Comparison {
    pub term: GeneralTerm,
    pub guards: Vec<Guard>,
}

impl_node!(Comparison, Format, ComparisonParser);

impl Comparison {
    pub fn individuals(&self) -> impl Iterator<Item = (&GeneralTerm, &Relation, &GeneralTerm)> {
        struct Individuals<'a> {
            lhs: &'a GeneralTerm,
            guards_iter: std::slice::Iter<'a, Guard>,
        }

        impl<'a> Iterator for Individuals<'a> {
            type Item = (&'a GeneralTerm, &'a Relation, &'a GeneralTerm);

            fn next(&mut self) -> Option<Self::Item> {
                if let Some(Guard {
                    relation,
                    term: rhs,
                }) = self.guards_iter.next()
                {
                    let result = Some((self.lhs, relation, rhs));
                    self.lhs = rhs;
                    result
                } else {
                    None
                }
            }
        }

        Individuals {
            lhs: &self.term,
            guards_iter: self.guards.iter(),
        }
    }

    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        let lhs = self.term.substitute(var.clone(), term.clone());

        let mut guards = Vec::new();
        for old_guard in self.guards {
            let new_guard = Guard {
                relation: old_guard.relation,
                term: old_guard.term.substitute(var.clone(), term.clone()),
            };
            guards.push(new_guard);
        }

        Comparison { term: lhs, guards }
    }

    fn rename_conflicting_symbols(self, possible_conflicts: &IndexSet<Predicate>) -> Self {
        let term = self.term.rename_conflicting_symbols(possible_conflicts);

        let mut guards = Vec::new();
        for old_guard in self.guards {
            let new_guard = Guard {
                relation: old_guard.relation,
                term: old_guard
                    .term
                    .rename_conflicting_symbols(possible_conflicts),
            };
            guards.push(new_guard);
        }

        Comparison { term, guards }
    }

    pub fn replace_placeholders(self, mapping: &IndexMap<String, FunctionConstant>) -> Self {
        Comparison {
            term: self.term.replace_placeholders(mapping),
            guards: self
                .guards
                .into_iter()
                .map(|g| g.replace_placeholders(mapping))
                .collect(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum AtomicFormula {
    Truth,
    Falsity,
    Atom(Atom),
    Comparison(Comparison),
}

impl_node!(AtomicFormula, Format, AtomicFormulaParser);

impl AtomicFormula {
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth => IndexSet::new(),
            AtomicFormula::Atom(a) => {
                let mut vars = IndexSet::new();
                for t in a.terms.iter() {
                    vars.extend(t.variables());
                }
                vars
            }
            AtomicFormula::Comparison(c) => {
                let mut vars = c.term.variables();
                for guard in c.guards.iter() {
                    vars.extend(guard.variables())
                }
                vars
            }
        }
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth | AtomicFormula::Comparison(_) => {
                IndexSet::new()
            }
            AtomicFormula::Atom(a) => IndexSet::from([a.predicate()]),
        }
    }

    pub fn symbols(&self) -> IndexSet<String> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth => IndexSet::new(),
            AtomicFormula::Atom(a) => {
                let mut symbols = IndexSet::new();
                for t in a.terms.iter() {
                    symbols.extend(t.symbols());
                }
                symbols
            }
            AtomicFormula::Comparison(c) => {
                let mut symbols = c.term.symbols();
                for guard in c.guards.iter() {
                    symbols.extend(guard.symbols())
                }
                symbols
            }
        }
    }

    pub fn function_constants(&self) -> IndexSet<FunctionConstant> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth => IndexSet::new(),
            AtomicFormula::Atom(a) => {
                let mut function_constants = IndexSet::new();
                for t in a.terms.iter() {
                    function_constants.extend(t.function_constants());
                }
                function_constants
            }
            AtomicFormula::Comparison(c) => {
                let mut function_constants = c.term.function_constants();
                for guard in c.guards.iter() {
                    function_constants.extend(guard.function_constants())
                }
                function_constants
            }
        }
    }

    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        match self {
            AtomicFormula::Atom(a) => AtomicFormula::Atom(a.substitute(var, term)),
            AtomicFormula::Comparison(c) => AtomicFormula::Comparison(c.substitute(var, term)),
            f => f,
        }
    }

    fn rename_conflicting_symbols(self, possible_conflicts: &IndexSet<Predicate>) -> Self {
        match self {
            AtomicFormula::Atom(a) => {
                AtomicFormula::Atom(a.rename_conflicting_symbols(possible_conflicts))
            }
            AtomicFormula::Comparison(c) => {
                AtomicFormula::Comparison(c.rename_conflicting_symbols(possible_conflicts))
            }
            x => x,
        }
    }

    pub fn replace_placeholders(self, mapping: &IndexMap<String, FunctionConstant>) -> Self {
        match self {
            AtomicFormula::Atom(a) => AtomicFormula::Atom(a.replace_placeholders(mapping)),
            AtomicFormula::Comparison(c) => {
                AtomicFormula::Comparison(c.replace_placeholders(mapping))
            }
            x => x,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryConnective {
    Negation,
}

impl_node!(UnaryConnective, Format, UnaryConnectiveParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Quantifier {
    Forall,
    Exists,
}

impl_node!(Quantifier, Format, QuantifierParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Quantification {
    pub quantifier: Quantifier,
    pub variables: Vec<Variable>,
}

impl_node!(Quantification, Format, QuantificationParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Sort {
    General,
    Integer,
    Symbol,
}

impl_node!(Sort, Format, SortParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct FunctionConstant {
    pub name: String,
    pub sort: Sort,
}

impl_node!(FunctionConstant, Format, FunctionConstantParser);

impl From<PlaceholderDeclaration> for FunctionConstant {
    fn from(value: PlaceholderDeclaration) -> Self {
        FunctionConstant {
            name: value.name,
            sort: value.sort,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Variable {
    pub name: String,
    pub sort: Sort,
}

impl_node!(Variable, Format, VariableParser);

impl TryFrom<GeneralTerm> for Variable {
    type Error = GeneralTerm;

    fn try_from(term: GeneralTerm) -> std::result::Result<Self, Self::Error> {
        match term {
            GeneralTerm::Variable(v) => Ok(Variable {
                name: v,
                sort: Sort::General,
            }),
            GeneralTerm::IntegerTerm(IntegerTerm::Variable(v)) => Ok(Variable {
                name: v,
                sort: Sort::Integer,
            }),
            GeneralTerm::SymbolicTerm(SymbolicTerm::Variable(v)) => Ok(Variable {
                name: v,
                sort: Sort::Symbol,
            }),
            x => Err(x),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinaryConnective {
    Conjunction,
    Disjunction,
    Implication,
    ReverseImplication,
    Equivalence,
}

impl_node!(BinaryConnective, Format, BinaryConnectiveParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Formula {
    AtomicFormula(AtomicFormula),
    UnaryFormula {
        connective: UnaryConnective,
        formula: Box<Formula>,
    },
    BinaryFormula {
        connective: BinaryConnective,
        lhs: Box<Formula>,
        rhs: Box<Formula>,
    },
    QuantifiedFormula {
        quantification: Quantification,
        formula: Box<Formula>,
    },
}

impl_node!(Formula, Format, FormulaParser);

impl Formula {
    /// Recursively turn a list of formulas into a conjunction tree
    pub fn conjoin(formulas: impl IntoIterator<Item = Formula>) -> Formula {
        /*
         * One could also implement this recursively:
         *
         * Case 1: List of formulas is empty
         * -> Return #true
         *
         * Case 2: List of formulas contains a single formula
         * -> Return that formula
         *
         * Case 3: List of formulas contains more than a single formula
         * -> Return conjoin(formula[0..n-2]) and formula[n-1]
         */

        formulas
            .into_iter()
            .reduce(|acc, e| Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: acc.into(),
                rhs: e.into(),
            })
            .unwrap_or(Formula::AtomicFormula(AtomicFormula::Truth))
    }

    /// Recursively turn a list of formulas into a tree of disjunctions
    pub fn disjoin(formulas: impl IntoIterator<Item = Formula>) -> Formula {
        /*
         * One could also implement this recursively:
         *
         * Case 1: List of formulas is empty
         * -> Return #false
         *
         * Case 2: List of formulas contains a single formula
         * -> Return that formula
         *
         * Case 3: List of formulas contains more than a single formula
         * -> Return conjoin(formula[0..n-2]) or formula[n-1]
         */

        formulas
            .into_iter()
            .reduce(|acc, e| Formula::BinaryFormula {
                connective: BinaryConnective::Disjunction,
                lhs: acc.into(),
                rhs: e.into(),
            })
            .unwrap_or(Formula::AtomicFormula(AtomicFormula::Falsity))
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            Formula::AtomicFormula(f) => f.variables(),
            Formula::UnaryFormula { formula, .. } => formula.variables(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars
            }
            Formula::QuantifiedFormula { formula, .. } => formula.variables(),
        }
    }

    pub fn free_variables(&self) -> IndexSet<Variable> {
        match &self {
            Formula::AtomicFormula(f) => f.variables(),
            Formula::UnaryFormula { formula, .. } => formula.free_variables(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.free_variables();
                vars.extend(rhs.free_variables());
                vars
            }
            Formula::QuantifiedFormula {
                quantification,
                formula,
            } => {
                let mut vars = formula.free_variables();
                for var in &quantification.variables {
                    vars.shift_remove(var);
                }
                vars
            }
        }
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        match &self {
            Formula::AtomicFormula(f) => f.predicates(),
            Formula::UnaryFormula { formula, .. } => formula.predicates(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.predicates();
                vars.extend(rhs.predicates());
                vars
            }
            Formula::QuantifiedFormula { formula, .. } => formula.predicates(),
        }
    }

    pub fn symbols(&self) -> IndexSet<String> {
        match &self {
            Formula::AtomicFormula(f) => f.symbols(),
            Formula::UnaryFormula { formula, .. } => formula.symbols(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.symbols();
                vars.extend(rhs.symbols());
                vars
            }
            Formula::QuantifiedFormula { formula, .. } => formula.symbols(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<FunctionConstant> {
        match &self {
            Formula::AtomicFormula(f) => f.function_constants(),
            Formula::UnaryFormula { formula, .. } => formula.function_constants(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.function_constants();
                vars.extend(rhs.function_constants());
                vars
            }
            Formula::QuantifiedFormula { formula, .. } => formula.function_constants(),
        }
    }

    // Replace all free occurences of var with term within the formula
    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        match self {
            Formula::AtomicFormula(f) => Formula::AtomicFormula(f.substitute(var, term)),
            Formula::UnaryFormula {
                connective,
                formula,
            } => Formula::UnaryFormula {
                connective,
                formula: formula.substitute(var, term).into(),
            },
            Formula::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => Formula::BinaryFormula {
                connective,
                lhs: lhs.substitute(var.clone(), term.clone()).into(),
                rhs: rhs.substitute(var, term).into(),
            },
            Formula::QuantifiedFormula {
                quantification,
                formula,
            } if !quantification.variables.contains(&var) => Formula::QuantifiedFormula {
                quantification,
                formula: formula.substitute(var, term).into(),
            },
            f @ Formula::QuantifiedFormula {
                quantification: _,
                formula: _,
            } => f,
        }
    }

    pub fn quantify(self, quantifier: Quantifier, variables: Vec<Variable>) -> Formula {
        if variables.is_empty() {
            self
        } else {
            Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier,
                    variables,
                },
                formula: Box::new(self),
            }
        }
    }

    pub fn universal_closure(self) -> Formula {
        let variables = self.free_variables().into_iter().collect();
        self.quantify(Quantifier::Forall, variables)
    }

    pub fn universal_closure_with_quantifier_joining(self) -> Formula {
        join_nested_quantifiers(self.universal_closure())
    }

    pub fn rename_conflicting_symbols(self, possible_conflicts: &IndexSet<Predicate>) -> Formula {
        match self {
            Formula::AtomicFormula(a) => {
                Formula::AtomicFormula(a.rename_conflicting_symbols(possible_conflicts))
            }
            Formula::UnaryFormula {
                connective,
                formula,
            } => Formula::UnaryFormula {
                connective,
                formula: formula
                    .rename_conflicting_symbols(possible_conflicts)
                    .into(),
            },
            Formula::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => Formula::BinaryFormula {
                connective,
                lhs: lhs.rename_conflicting_symbols(possible_conflicts).into(),
                rhs: rhs.rename_conflicting_symbols(possible_conflicts).into(),
            },
            Formula::QuantifiedFormula {
                quantification,
                formula,
            } => Formula::QuantifiedFormula {
                quantification,
                formula: formula
                    .rename_conflicting_symbols(possible_conflicts)
                    .into(),
            },
        }
    }

    pub fn replace_placeholders(self, mapping: &IndexMap<String, FunctionConstant>) -> Self {
        self.apply(&mut |formula| match formula {
            Formula::AtomicFormula(a) => Formula::AtomicFormula(a.replace_placeholders(mapping)),
            x => x,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, IntoIterator)]
pub struct Theory {
    #[into_iterator(owned, ref, ref_mut)]
    pub formulas: Vec<Formula>,
}

impl_node!(Theory, Format, TheoryParser);

impl Theory {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut preds = IndexSet::new();
        for formula in self {
            preds.extend(formula.predicates())
        }
        preds
    }

    pub fn replace_placeholders(self, mapping: &IndexMap<String, FunctionConstant>) -> Self {
        self.into_iter()
            .map(|f| f.replace_placeholders(mapping))
            .collect()
    }
}

impl FromIterator<Formula> for Theory {
    fn from_iter<T: IntoIterator<Item = Formula>>(iter: T) -> Self {
        Theory {
            formulas: iter.into_iter().collect(),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Role {
    Assumption,
    Spec,
    Lemma,
    Definition,
    InductiveLemma,
}

impl_node!(Role, Format, RoleParser);

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, Hash, ValueEnum)]
pub enum Direction {
    #[default]
    Universal,
    Forward,
    Backward,
}

impl_node!(Direction, Format, DirectionParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AnnotatedFormula {
    pub role: Role,
    pub direction: Direction,
    pub name: String,
    pub formula: Formula,
}

impl_node!(AnnotatedFormula, Format, AnnotatedFormulaParser);

impl AnnotatedFormula {
    pub fn into_problem_formula(self, role: problem::Role) -> problem::AnnotatedFormula {
        problem::AnnotatedFormula {
            // TODO: Revisit default naming scheme!
            name: self.name,
            role,
            formula: self.formula,
        }
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        self.formula.predicates()
    }

    pub fn universal_closure(&self) -> Self {
        AnnotatedFormula {
            role: self.role,
            direction: self.direction,
            name: self.name.clone(),
            formula: self.formula.clone().universal_closure(),
        }
    }

    pub fn universal_closure_with_quantifier_joining(&self) -> Self {
        AnnotatedFormula {
            role: self.role,
            direction: self.direction,
            name: self.name.clone(),
            formula: self
                .formula
                .clone()
                .universal_closure_with_quantifier_joining(),
        }
    }

    pub fn replace_placeholders(mut self, mapping: &IndexMap<String, FunctionConstant>) -> Self {
        self.formula = self.formula.replace_placeholders(mapping);
        self
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, IntoIterator)]
pub struct Specification {
    #[into_iterator(owned, ref, ref_mut)]
    pub formulas: Vec<AnnotatedFormula>,
}

impl_node!(Specification, Format, SpecificationParser);

impl Specification {
    pub fn empty() -> Self {
        Specification { formulas: vec![] }
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for formula in &self.formulas {
            predicates.extend(formula.predicates())
        }
        predicates
    }

    pub fn replace_placeholders(self, mapping: &IndexMap<String, FunctionConstant>) -> Self {
        self.into_iter()
            .map(|f| f.replace_placeholders(mapping))
            .collect()
    }
}

impl FromIterator<AnnotatedFormula> for Specification {
    fn from_iter<T: IntoIterator<Item = AnnotatedFormula>>(iter: T) -> Self {
        Specification {
            formulas: iter.into_iter().collect(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct PlaceholderDeclaration {
    pub name: String,
    pub sort: Sort,
}

impl_node!(PlaceholderDeclaration, Format, PlaceholderDeclarationParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum UserGuideEntry {
    InputPredicate(Predicate),
    OutputPredicate(Predicate),
    PlaceholderDeclaration(PlaceholderDeclaration),
    AnnotatedFormula(AnnotatedFormula),
}

impl_node!(UserGuideEntry, Format, UserGuideEntryParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash, IntoIterator)]
pub struct UserGuide {
    #[into_iterator(owned, ref, ref_mut)]
    pub entries: Vec<UserGuideEntry>,
}

impl_node!(UserGuide, Format, UserGuideParser);

impl UserGuide {
    pub fn input_predicates(&self) -> IndexSet<Predicate> {
        let mut result = IndexSet::new();
        for entry in &self.entries {
            if let UserGuideEntry::InputPredicate(p) = entry {
                result.insert(p.clone());
            }
        }
        result
    }

    pub fn output_predicates(&self) -> IndexSet<Predicate> {
        let mut result = IndexSet::new();
        for entry in &self.entries {
            if let UserGuideEntry::OutputPredicate(p) = entry {
                result.insert(p.clone());
            }
        }
        result
    }

    pub fn public_predicates(&self) -> IndexSet<Predicate> {
        let mut result = self.input_predicates();
        result.extend(self.output_predicates());
        result
    }

    pub fn placeholders(&self) -> IndexSet<FunctionConstant> {
        let mut result = IndexSet::new();
        for entry in &self.entries {
            if let UserGuideEntry::PlaceholderDeclaration(p) = entry {
                let fc = FunctionConstant::from(p.clone());
                result.insert(fc);
            }
        }
        result
    }

    pub fn formulas(&self) -> Vec<AnnotatedFormula> {
        let mut result = Vec::new();
        for entry in &self.entries {
            if let UserGuideEntry::AnnotatedFormula(p) = entry {
                result.push(p.clone());
            }
        }
        result
    }
}

impl FromIterator<UserGuideEntry> for UserGuide {
    fn from_iter<T: IntoIterator<Item = UserGuideEntry>>(iter: T) -> Self {
        UserGuide {
            entries: iter.into_iter().collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use {super::Formula, indexmap::IndexSet};

    #[test]
    fn test_formula_conjoin() {
        for (src, target) in [
            (vec![], "#true"),
            (vec!["X = Y"], "X = Y"),
            (vec!["X = Y", "p(a)", "q(X)"], "(X = Y and p(a)) and q(X)"),
        ] {
            assert_eq!(
                Formula::conjoin(src.iter().map(|x| x.parse().unwrap())),
                target.parse().unwrap(),
            )
        }
    }

    #[test]
    fn test_formula_disjoin() {
        for (src, target) in [
            (vec![], "#false"),
            (vec!["X = Y"], "X = Y"),
            (vec!["X = Y", "p(a)", "q(X)"], "(X = Y or p(a)) or q(X)"),
        ] {
            assert_eq!(
                Formula::disjoin(src.iter().map(|x| x.parse().unwrap())),
                target.parse().unwrap(),
            )
        }
    }

    #[test]
    fn test_formula_free_variables() {
        for (src, target) in [
            ("forall X (X = Y)", vec!["Y"]),
            ("forall X (X = Y) and Y = Z", vec!["Y", "Z"]),
            ("forall X exists Y (X = Y)", vec![]),
        ] {
            assert_eq!(
                src.parse::<Formula>().unwrap().free_variables(),
                target
                    .iter()
                    .map(|x| x.parse().unwrap())
                    .collect::<IndexSet<_>>(),
            )
        }
    }

    #[test]
    fn test_formula_substitute() {
        for (src, var, term, target) in [
            ("p(X)", "X", "s", "p(s)"),
            ("p(X)", "X", "5", "p(5)"),
            ("prime(-X$i + 13)", "X$i", "3*Y$i", "prime(-(3*Y$i) + 13)"),
            ("prime(X$i, X)", "X$i", "Y$i", "prime(Y$i, X)"),
            ("exists X (X = Y)", "Y", "3", "exists X (X = 3)"),
            ("forall X p(X)", "X", "1", "forall X p(X)"),
            (
                "exists X (X = Y)",
                "Y",
                "X$i + 3",
                "exists X (X = (X$i + 3))",
            ),
            (
                "forall X (q(Y) or exists Y (p(1,Y) and X > Y))",
                "Y",
                "a",
                "forall X (q(a) or exists Y (p(1,Y) and X > Y))",
            ),
            (
                "forall X (q(Y$i) or exists Z (p(1,Z) and X > Y$i > Z))",
                "Y$i",
                "4",
                "forall X (q(4) or exists Z (p(1,Z) and X > 4 > Z))",
            ),
            (
                "exists J$i (J$i = N$i and Z = Z1)",
                "Z",
                "I",
                "exists J$i (J$i = N$i and I = Z1)",
            ),
        ] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .substitute(var.parse().unwrap(), term.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }
}
