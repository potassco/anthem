use {
    crate::{
        formatting::asp::default::Format,
        parsing::asp::pest::{
            BodyParser,
            HeadParser, ProgramParser,
            RuleParser, UnaryOperatorParser,
        },
        syntax_tree::{Node, impl_node},
    },
    derive_more::derive::IntoIterator,
    indexmap::IndexSet,
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryOperator {
    Negative,
    AbsoluteValue,
}

impl_node!(UnaryOperator, Format, UnaryOperatorParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ConditionalHead {
    AtomicFormula(AtomicFormula),
    Falsity,
}

impl_node!(ConditionalHead, Format, ConditionalHeadParser);

impl ConditionalHead {
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            ConditionalHead::AtomicFormula(a) => a.variables(),
            ConditionalHead::Falsity => IndexSet::new(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            ConditionalHead::AtomicFormula(a) => a.function_constants(),
            ConditionalHead::Falsity => IndexSet::new(),
        }
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        match &self {
            ConditionalHead::AtomicFormula(a) => a.predicates(),
            ConditionalHead::Falsity => IndexSet::new(),
        }
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        match &self {
            ConditionalHead::AtomicFormula(a) => a.positive_predicates(),
            ConditionalHead::Falsity => IndexSet::new(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ConditionalBody {
    pub formulas: Vec<AtomicFormula>,
}

impl_node!(ConditionalBody, Format, ConditionalBodyParser);

impl ConditionalBody {
    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for f in self.formulas.iter() {
            vars.extend(f.variables());
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut constants = IndexSet::new();
        for f in self.formulas.iter() {
            constants.extend(f.function_constants());
        }
        constants
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for f in self.formulas.iter() {
            predicates.extend(f.predicates());
        }
        predicates
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for f in self.formulas.iter() {
            predicates.extend(f.positive_predicates());
        }
        predicates
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ConditionalLiteral {
    pub head: ConditionalHead,
    pub conditions: ConditionalBody,
}

impl_node!(ConditionalLiteral, Format, ConditionalLiteralParser);

impl ConditionalLiteral {
    pub fn basic(&self) -> bool {
        self.conditions.formulas.is_empty()
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.head.variables();
        vars.extend(self.conditions.variables());
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut constants = self.head.function_constants();
        constants.extend(self.conditions.function_constants());
        constants
    }

    pub fn global_variables(&self) -> IndexSet<Variable> {
        let mut head_vars = self.head.variables();
        let body_vars = self.conditions.variables();
        head_vars.retain(|v| !body_vars.contains(v));
        head_vars
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = self.head.predicates();
        predicates.extend(self.conditions.predicates());
        predicates
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = self.head.positive_predicates();
        predicates.extend(self.conditions.positive_predicates());
        predicates
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

#[derive(Clone, Debug, Eq, PartialEq, Hash, IntoIterator)]
pub struct Body {
    #[into_iterator(owned, ref, ref_mut)]
    pub formulas: Vec<ConditionalLiteral>,
}

impl_node!(Body, Format, BodyParser);

impl Body {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for formula in self.formulas.iter() {
            predicates.extend(formula.predicates())
        }
        predicates
    }

    pub fn positive_predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for formula in self.formulas.iter() {
            predicates.extend(formula.positive_predicates())
        }
        predicates
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for formula in self.formulas.iter() {
            vars.extend(formula.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = IndexSet::new();
        for formula in self.formulas.iter() {
            functions.extend(formula.function_constants())
        }
        functions
    }
}

impl FromIterator<ConditionalLiteral> for Body {
    fn from_iter<T: IntoIterator<Item = ConditionalLiteral>>(iter: T) -> Self {
        Body {
            formulas: iter.into_iter().collect(),
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

    pub fn global_variables(&self) -> IndexSet<Variable> {
        let mut vars = self.head.variables();
        for formula in self.body.formulas.iter() {
            vars.extend(formula.global_variables());
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = self.head.function_constants();
        functions.extend(self.body.function_constants());
        functions
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
}

impl FromIterator<Rule> for Program {
    fn from_iter<T: IntoIterator<Item = Rule>>(iter: T) -> Self {
        Program {
            rules: iter.into_iter().collect(),
        }
    }
}
