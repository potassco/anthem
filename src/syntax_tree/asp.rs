use {
    crate::{
        formatting::asp::default::Format,
        parsing::asp::pest::{
            AggregateAtomParser, AggregateParser, AtomParser, AtomicFormulaParser,
            BinaryOperatorParser, BodyLiteralParser, BodyParser, ComparisonParser, HeadParser,
            LiteralParser, PrecomputedTermParser, PredicateParser, ProgramParser, RelationParser,
            RuleParser, SignParser, TermParser, UnaryOperatorParser, VariableParser,
        },
        syntax_tree::{Node, impl_node},
    },
    derive_more::derive::IntoIterator,
    indexmap::IndexSet,
    std::collections::HashMap,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum PrecomputedTerm {
    Infimum,
    Numeral(isize),
    Symbol(String),
    Supremum,
}

impl PrecomputedTerm {
    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            PrecomputedTerm::Infimum => IndexSet::new(),
            PrecomputedTerm::Numeral(_) => IndexSet::new(),
            PrecomputedTerm::Symbol(s) => IndexSet::from([s.clone()]),
            PrecomputedTerm::Supremum => IndexSet::new(),
        }
    }
}

impl_node!(PrecomputedTerm, Format, PrecomputedTermParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Variable(pub String);

impl_node!(Variable, Format, VariableParser);

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryOperator {
    Negative,
}

impl_node!(UnaryOperator, Format, UnaryOperatorParser);

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Interval,
}

impl_node!(BinaryOperator, Format, BinaryOperatorParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Term {
    PrecomputedTerm(PrecomputedTerm),
    Variable(Variable),
    UnaryOperation {
        op: UnaryOperator,
        arg: Box<Term>,
    },
    BinaryOperation {
        op: BinaryOperator,
        lhs: Box<Term>,
        rhs: Box<Term>,
    },
}

impl_node!(Term, Format, TermParser);

impl From<Variable> for Term {
    fn from(value: Variable) -> Self {
        Term::Variable(value)
    }
}

impl Term {
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            Term::PrecomputedTerm(_) => IndexSet::new(),
            Term::Variable(v) => IndexSet::from([v.clone()]),
            Term::UnaryOperation { arg, .. } => arg.variables(),
            Term::BinaryOperation { lhs, rhs, .. } => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars
            }
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            Term::PrecomputedTerm(t) => t.function_constants(),
            Term::Variable(_) => IndexSet::new(),
            Term::UnaryOperation { arg, .. } => arg.function_constants(),
            Term::BinaryOperation { lhs, rhs, .. } => {
                let mut functions = lhs.function_constants();
                functions.extend(rhs.function_constants());
                functions
            }
        }
    }

    pub fn contains_interval(&self) -> bool {
        match self {
            Term::PrecomputedTerm(_) | Term::Variable(_) => false,
            Term::UnaryOperation { arg, .. } => arg.contains_interval(),
            Term::BinaryOperation { op, lhs, rhs } => match op {
                BinaryOperator::Interval => true,
                _ => lhs.contains_interval() || rhs.contains_interval(),
            },
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Predicate {
    pub symbol: String,
    pub arity: usize,
}

impl_node!(Predicate, Format, PredicateParser);

impl From<crate::syntax_tree::fol::Predicate> for Predicate {
    fn from(value: crate::syntax_tree::fol::Predicate) -> Self {
        Predicate {
            symbol: value.symbol,
            arity: value.arity,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Atom {
    pub predicate_symbol: String,
    pub terms: Vec<Term>,
}

impl_node!(Atom, Format, AtomParser);

impl Atom {
    pub fn predicate(&self) -> Predicate {
        Predicate {
            symbol: self.predicate_symbol.clone(),
            arity: self.terms.len(),
        }
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for term in self.terms.iter() {
            vars.extend(term.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = IndexSet::new();
        for term in self.terms.iter() {
            functions.extend(term.function_constants())
        }
        functions
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Sign {
    NoSign,
    Negation,
    DoubleNegation,
}

impl_node!(Sign, Format, SignParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Literal {
    pub sign: Sign,
    pub atom: Atom,
}

impl_node!(Literal, Format, LiteralParser);

impl Literal {
    pub fn predicate(&self) -> Predicate {
        self.atom.predicate()
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        self.atom.variables()
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        self.atom.function_constants()
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Relation {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

impl_node!(Relation, Format, RelationParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Comparison {
    pub relation: Relation,
    pub lhs: Term,
    pub rhs: Term,
}

impl_node!(Comparison, Format, ComparisonParser);

impl Comparison {
    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.lhs.variables();
        vars.extend(self.rhs.variables());
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = self.lhs.function_constants();
        functions.extend(self.rhs.function_constants());
        functions
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum AtomicFormula {
    Literal(Literal),
    Comparison(Comparison),
}

impl_node!(AtomicFormula, Format, AtomicFormulaParser);

impl AtomicFormula {
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            AtomicFormula::Literal(l) => l.variables(),
            AtomicFormula::Comparison(c) => c.variables(),
        }
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        match &self {
            AtomicFormula::Literal(l) => IndexSet::from([l.predicate()]),
            AtomicFormula::Comparison(_) => IndexSet::new(),
        }
    }

    fn positive_predicates(&self) -> IndexSet<Predicate> {
        match &self {
            AtomicFormula::Literal(Literal {
                sign: Sign::NoSign,
                atom,
            }) => IndexSet::from([atom.predicate()]),
            AtomicFormula::Literal(_) | AtomicFormula::Comparison(_) => IndexSet::new(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            AtomicFormula::Literal(l) => l.function_constants(),
            AtomicFormula::Comparison(c) => c.function_constants(),
        }
    }

    pub fn terms(&self) -> IndexSet<Term> {
        match &self {
            AtomicFormula::Literal(l) => l.atom.terms.iter().cloned().collect(),
            AtomicFormula::Comparison(c) => IndexSet::from([c.lhs.clone(), c.rhs.clone()]),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[non_exhaustive]
pub enum AggregateOperation {
    Count,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Aggregate {
    pub operation: AggregateOperation,
    pub variable_list: Vec<Variable>,
    pub conditions: Vec<AtomicFormula>,
}

impl_node!(Aggregate, Format, AggregateParser);

impl Aggregate {
    pub fn is_valid_counting_aggregate(&self) -> bool {
        let mut valid = true;

        // X is a distinct tuple of variables
        let unique_vars: IndexSet<Variable> = IndexSet::from_iter(self.variable_list.clone());
        if unique_vars.len() < self.variable_list.len() {
            valid = false;
        }

        // Every member of X must occur in L for aggregate element X : L
        let mut condition_vars = IndexSet::new();
        for formula in &self.conditions {
            for var in formula.variables() {
                condition_vars.insert(var);
            }
        }
        if unique_vars.difference(&condition_vars).next().is_some() {
            valid = false;
        }

        valid
    }

    fn terms(&self) -> IndexSet<Term> {
        let mut terms = IndexSet::from_iter(self.variable_list.iter().cloned().map(|v| v.into()));
        for formula in self.conditions.iter() {
            terms.extend(formula.terms());
        }
        terms
    }

    fn function_constants(&self) -> IndexSet<String> {
        let mut function_constants = IndexSet::new();
        for formula in self.conditions.iter() {
            function_constants.extend(formula.function_constants());
        }
        function_constants
    }

    fn variables(&self) -> IndexSet<Variable> {
        let mut variables = IndexSet::from_iter(self.variable_list.iter().cloned());
        for formula in self.conditions.iter() {
            variables.extend(formula.variables());
        }
        variables
    }

    pub(crate) fn condition_variables(&self) -> IndexSet<Variable> {
        let mut variables = IndexSet::new();
        for formula in self.conditions.iter() {
            variables.extend(formula.variables());
        }
        variables
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
#[non_exhaustive]
pub enum AggregateOrder {
    Left,
    Right,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AggregateAtom {
    pub aggregate: Aggregate,
    pub relation: Relation,
    pub guard: Term,
    pub order: AggregateOrder,
}

impl_node!(AggregateAtom, Format, AggregateAtomParser);

impl AggregateAtom {
    pub fn is_valid_counting_atom(&self) -> bool {
        let mut valid = true;

        if !self.aggregate.is_valid_counting_aggregate() {
            valid = false
        }

        // Only leq and geq are allowed in agg atoms
        match (self.relation, self.order) {
            (Relation::LessEqual, AggregateOrder::Left)
            | (Relation::GreaterEqual, AggregateOrder::Left) => (),
            _ => {
                valid = false;
            }
        }

        // count{E} prec t requires that t is interval-free
        if self.guard.contains_interval() {
            valid = false;
        }

        valid
    }

    // all variables in the tuple X are local for aggregate element X : L
    pub fn all_local(&self, globals: &IndexSet<Variable>) -> bool {
        let mut all_local = true;

        for var in &self.aggregate.variable_list {
            if globals.contains(var) {
                all_local = false;
            }
        }

        all_local
    }

    pub fn terms(&self) -> IndexSet<Term> {
        let mut terms = IndexSet::new();
        terms.insert(self.guard.clone());
        terms.extend(self.aggregate.terms());
        terms
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut function_constants = self.guard.function_constants();
        function_constants.extend(self.aggregate.function_constants());
        function_constants
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut variables = self.guard.variables();
        variables.extend(self.aggregate.variables());
        variables
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for formula in self.aggregate.conditions.iter() {
            predicates.extend(formula.predicates());
        }
        predicates
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        let mut positive_predicates = IndexSet::new();
        for formula in self.aggregate.conditions.iter() {
            positive_predicates.extend(formula.positive_predicates());
        }
        positive_predicates
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Head {
    Basic(Atom),
    Choice(Atom),
    Falsity,
}

impl_node!(Head, Format, HeadParser);

impl Head {
    pub fn predicate(&self) -> Option<Predicate> {
        match self {
            Head::Basic(a) => Some(a.predicate()),
            Head::Choice(a) => Some(a.predicate()),
            Head::Falsity => None,
        }
    }

    // TODO: Revisit these helper function; make sure they are symmetric with all the others.

    pub fn terms(&self) -> Option<&[Term]> {
        match self {
            Head::Basic(a) => Some(&a.terms),
            Head::Choice(a) => Some(&a.terms),
            Head::Falsity => None,
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Head::Basic(a) => a.terms.len(),
            Head::Choice(a) => a.terms.len(),
            Head::Falsity => 0,
        }
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            Head::Basic(a) | Head::Choice(a) => a.variables(),
            Head::Falsity => IndexSet::new(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            Head::Basic(a) | Head::Choice(a) => a.function_constants(),
            Head::Falsity => IndexSet::new(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BodyLiteral {
    AtomicFormula(AtomicFormula),
    AggregateAtom(AggregateAtom),
}

impl_node!(BodyLiteral, Format, BodyLiteralParser);

impl BodyLiteral {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        match self {
            BodyLiteral::AtomicFormula(formula) => formula.predicates(),
            BodyLiteral::AggregateAtom(atom) => atom.predicates(),
        }
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        match self {
            BodyLiteral::AtomicFormula(formula) => formula.positive_predicates(),
            BodyLiteral::AggregateAtom(atom) => atom.positive_predicates(),
        }
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        match self {
            BodyLiteral::AtomicFormula(formula) => formula.variables(),
            BodyLiteral::AggregateAtom(atom) => atom.variables(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match self {
            BodyLiteral::AtomicFormula(formula) => formula.function_constants(),
            BodyLiteral::AggregateAtom(atom) => atom.function_constants(),
        }
    }

    pub fn terms(&self) -> IndexSet<Term> {
        match self {
            BodyLiteral::AtomicFormula(formula) => formula.terms(),
            BodyLiteral::AggregateAtom(atom) => atom.terms(),
        }
    }

    fn global_variables(&self) -> IndexSet<Variable> {
        match self {
            BodyLiteral::AtomicFormula(formula) => formula.variables(),
            BodyLiteral::AggregateAtom(atom) => atom.guard.variables(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, IntoIterator)]
pub struct Body {
    #[into_iterator(owned, ref, ref_mut)]
    pub literals: Vec<BodyLiteral>,
}

impl_node!(Body, Format, BodyParser);

impl Body {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for formula in self.literals.iter() {
            predicates.extend(formula.predicates())
        }
        predicates
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for formula in self.literals.iter() {
            predicates.extend(formula.positive_predicates())
        }
        predicates
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for formula in self.literals.iter() {
            vars.extend(formula.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = IndexSet::new();
        for formula in self.literals.iter() {
            functions.extend(formula.function_constants())
        }
        functions
    }

    pub fn terms(&self) -> IndexSet<Term> {
        let mut terms = IndexSet::new();
        for formula in self.literals.iter() {
            terms.extend(formula.terms())
        }
        terms
    }

    fn global_variables(&self) -> IndexSet<Variable> {
        let mut globals = IndexSet::new();
        for literal in self.literals.iter() {
            globals.extend(literal.global_variables());
        }
        globals
    }
}

impl FromIterator<BodyLiteral> for Body {
    fn from_iter<T: IntoIterator<Item = BodyLiteral>>(iter: T) -> Self {
        Body {
            literals: iter.into_iter().collect(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Rule {
    pub head: Head,
    pub body: Body,
}

impl_node!(Rule, Format, RuleParser);

impl Rule {
    pub fn global_variables(&self) -> IndexSet<Variable> {
        let mut globals = self.head.variables();
        globals.extend(self.body.global_variables());
        globals
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        if let Some(predicate) = self.head.predicate() {
            predicates.insert(predicate);
        }
        predicates.extend(self.body.predicates());
        predicates
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.head.variables();
        vars.extend(self.body.variables());
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = self.head.function_constants();
        functions.extend(self.body.function_constants());
        functions
    }

    pub fn terms(&self) -> IndexSet<Term> {
        let mut terms = IndexSet::new();
        if let Some(head_terms) = self.head.terms() {
            head_terms.iter().for_each(|term| {
                terms.insert(term.clone());
            });
        }
        terms.extend(self.body.terms());
        terms
    }

    // An occurrence of an aggregate atom is uniquely identified by
    // the variables and conditions of the atom and the list of global variables in the rule
    fn aggregate_formula_keys(&self) -> Vec<AggregateFormulaKey> {
        let mut keys = Vec::new();
        for literal in self.body.literals.iter() {
            if let BodyLiteral::AggregateAtom(atom) = literal {
                let globals = Vec::from_iter(self.global_variables());
                keys.push(AggregateFormulaKey {
                    variables: atom.aggregate.variable_list.clone(),
                    conditions: atom.aggregate.conditions.clone(),
                    globals,
                });
            }
        }
        keys
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, IntoIterator)]
pub struct Program {
    #[into_iterator(owned, ref, ref_mut)]
    pub rules: Vec<Rule>,
}

impl_node!(Program, Format, ProgramParser);

impl Program {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for rule in &self.rules {
            predicates.extend(rule.predicates())
        }
        predicates
    }

    pub fn head_predicates(&self) -> IndexSet<Predicate> {
        let mut result = IndexSet::new();
        for rule in &self.rules {
            if let Some(predicate) = rule.head.predicate() {
                result.insert(predicate.clone());
            }
        }
        result
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for rule in self.rules.iter() {
            vars.extend(rule.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = IndexSet::new();
        for rule in self.rules.iter() {
            functions.extend(rule.function_constants());
        }
        functions
    }

    // Map every aggregate atom occurring in the program to a unique id
    // used for naming Start, Atleast, Atmost formulas.
    // If two aggregate atoms have the same variable lists, conditions, and global variables,
    // then they are mapped to the same name - TODO: check this for accuracy
    pub(crate) fn aggregate_names(&self) -> AggregateNameMap {
        let mut program_map = HashMap::new();
        for rule in self.rules.iter() {
            for agg_key in rule.aggregate_formula_keys() {
                if !program_map.contains_key(&agg_key) {
                    program_map.insert(agg_key, max_value(&program_map) + 1);
                }
            }
        }
        program_map
    }
}

impl FromIterator<Rule> for Program {
    fn from_iter<T: IntoIterator<Item = Rule>>(iter: T) -> Self {
        Program {
            rules: iter.into_iter().collect(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AggregateFormulaKey {
    pub(crate) variables: Vec<Variable>,
    pub(crate) conditions: Vec<AtomicFormula>,
    pub(crate) globals: Vec<Variable>,
}

pub type AggregateNameMap = HashMap<AggregateFormulaKey, usize>;

fn max_value(map: &AggregateNameMap) -> usize {
    let mut max_val = 0;
    for value in map.values() {
        let val = *value;
        if val > max_val {
            max_val = val;
        }
    }
    max_val
}

#[cfg(test)]
mod tests {
    use {
        super::{
            Atom, AtomicFormula, Body, Comparison, Head, PrecomputedTerm, Program, Relation, Rule,
            Term,
        },
        crate::syntax_tree::asp::BodyLiteral,
        indexmap::IndexSet,
    };

    #[test]
    fn test_program_function_constants() {
        // p :- b != a.
        let program = Program {
            rules: vec![Rule {
                head: Head::Basic(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![],
                }),
                body: Body {
                    literals: vec![BodyLiteral::AtomicFormula(AtomicFormula::Comparison(
                        Comparison {
                            lhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())),
                            rhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("b".into())),
                            relation: Relation::NotEqual,
                        },
                    ))],
                },
            }],
        };
        assert_eq!(
            program.function_constants(),
            IndexSet::from(["a".into(), "b".into()])
        )
    }
}
