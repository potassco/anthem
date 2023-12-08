use {
    crate::{
        formatting::fol::default::Format,
        parsing::fol::pest::{
            AtomParser, AtomicFormulaParser, BasicIntegerTermParser, BinaryConnectiveParser,
            BinaryOperatorParser, ComparisonParser, FormulaParser, GeneralTermParser, GuardParser,
            IntegerTermParser, PredicateParser, QuantificationParser, QuantifierParser,
            RelationParser, TheoryParser, UnaryConnectiveParser, UnaryOperatorParser,
            VariableParser,
        },
        syntax_tree::{impl_node, Node},
    },
    std::{collections::HashSet, hash::Hash},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BasicIntegerTerm {
    Infimum,
    Supremum,
    Numeral(isize),
    IntegerVariable(String),
}

impl_node!(BasicIntegerTerm, Format, BasicIntegerTermParser);

impl BasicIntegerTerm {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            BasicIntegerTerm::IntegerVariable(v) => HashSet::from([Variable {
                name: v.to_string(),
                sort: Sort::Integer,
            }]),
            _ => HashSet::new(),
        }
    }
}

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
    BasicIntegerTerm(BasicIntegerTerm),
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
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            IntegerTerm::BasicIntegerTerm(t) => t.variables(),
            IntegerTerm::UnaryOperation { arg: t, .. } => t.variables(),
            IntegerTerm::BinaryOperation { lhs, rhs, .. } => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum GeneralTerm {
    Symbol(String),
    GeneralVariable(String),
    IntegerTerm(IntegerTerm),
}

impl_node!(GeneralTerm, Format, GeneralTermParser);

impl GeneralTerm {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            GeneralTerm::Symbol(_) => HashSet::new(),
            GeneralTerm::GeneralVariable(v) => HashSet::from([Variable {
                name: v.to_string(),
                sort: Sort::General,
            }]),
            GeneralTerm::IntegerTerm(t) => t.variables(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Predicate {
    pub symbol: String,
    pub arity: usize,
}

impl_node!(Predicate, Format, PredicateParser);

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
}

impl_node!(Atom, Format, AtomParser);

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
    pub fn variables(&self) -> HashSet<Variable> {
        self.term.variables()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Comparison {
    pub term: GeneralTerm,
    pub guards: Vec<Guard>,
}

impl_node!(Comparison, Format, ComparisonParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum AtomicFormula {
    Truth,
    Falsity,
    Atom(Atom),
    Comparison(Comparison),
}

impl_node!(AtomicFormula, Format, AtomicFormulaParser);

impl AtomicFormula {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth => HashSet::new(),
            AtomicFormula::Atom(a) => {
                let mut vars = HashSet::new();
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

    pub fn predicates(&self) -> HashSet<Predicate> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth | AtomicFormula::Comparison(_) => {
                HashSet::new()
            }
            AtomicFormula::Atom(a) => HashSet::from([a.predicate()]),
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
    Integer,
    General,
}

// TODO: Should Sort be a Node?

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Variable {
    pub name: String,
    pub sort: Sort,
}

impl_node!(Variable, Format, VariableParser);

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
    pub fn variables(&self) -> HashSet<Variable> {
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

    pub fn predicates(&self) -> HashSet<Predicate> {
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
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Theory {
    pub formulas: Vec<Formula>,
}

impl_node!(Theory, Format, TheoryParser);
