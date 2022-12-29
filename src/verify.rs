use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet},
    convert::TryFrom,
    ops::Deref,
    rc::Rc,
};

use crate::{ast::*, proof::*};

#[derive(thiserror::Error, Debug, PartialEq, Eq)]
pub enum Error {
    #[error("mismatched final stack for: {0}")]
    MismatchedStack(String),

    #[error("unrecognized label: {0}")]
    UnrecognizedLabel(String),

    #[error("unrecognized symbol: {0}")]
    UnrecognizedSymbol(String),

    #[error("exhausted stack trying to resolve: {0}")]
    ExhaustedStack(String),

    #[error("mismatched step, expected \n  {expected}\ngot \n  {got}")]
    MismatchedStep { expected: String, got: String },

    #[error("overlapping disjoint variables")]
    OverlappingDisjoint,

    #[error("specified variable {0:?} must be disjoint to itself")]
    SelfDisjoint(String),

    #[error("no type defined for variable: {0}")]
    NoVariableType(String),
}

pub fn verify(stmts: Vec<Stmt>) -> Result<(), Error> {
    let frame = compile(stmts)?;

    for t in &frame.theorems {
        let mut stack = Vec::<Sequence>::new();
        let mut heap = Vec::<Sequence>::new();

        let mandatory_hypotheses = t.hypotheses.iter().map(|h| h.as_str()).collect::<Vec<_>>();
        for step in t.proof.plain(&mandatory_hypotheses) {
            match step {
                Step::Label(step) => {
                    if let Some(unify) = frame.get_op(step) {
                        unify.apply_to(&mut stack, &frame.all_hypotheses)?;
                    } else if let Some(h) = frame.get_hypothesis(step) {
                        stack.push(Sequence {
                            type_code: h.type_code.clone(),
                            symbols: h.symbols.clone(),
                        });
                    } else {
                        return Err(Error::UnrecognizedLabel(step.to_string()));
                    }
                }
                Step::ToHeap => {
                    heap.push(stack.last().unwrap().clone());
                }
                Step::FromHeap(i) => {
                    stack.push(heap[i].clone());
                }
            }
        }

        let target = Sequence {
            type_code: t.type_code.clone(),
            symbols: t.symbols.clone(),
        };
        if stack != vec![target] {
            dbg!(&stack);
            return Err(Error::MismatchedStack(t.name.to_string()));
        }
    }

    Ok(())
}

fn compile(stmts: Vec<Stmt>) -> Result<Frame, Error> {
    let mut result = Frame::default();

    compile_into(stmts, &mut result, &mut Vec::new())?;

    Ok(result)
}

fn compile_into(
    stmts: Vec<Stmt>,
    frame: &mut Frame,
    scope_stack: &mut Vec<Scope>,
) -> Result<(), Error> {
    scope_stack.push(Scope::default());

    for stmt in stmts {
        match stmt {
            Stmt::ConstantDecl(c) => frame.consts.extend(c.into_iter().map(Symbol::from)),
            Stmt::VarDecl(v) => frame.vars.extend(v.into_iter().map(Symbol::from)),

            Stmt::Block(b) => compile_into(b, frame, scope_stack)?,

            Stmt::VarTypeDecl(f) => {
                // TODO(shelbyd): Check var is a var.
                let symbol = frame.resolve_symbol(f.var)?;
                let label = Label::from(f.name);

                frame.var_hypotheses.insert(symbol.clone(), label.clone());

                frame.ops.insert(
                    label,
                    Unify {
                        vars: OrderedVars::default(),
                        type_code: frame.resolve_symbol(f.type_code)?,
                        symbols: vec![symbol],
                        hypotheses: vec![],
                        disjoints: HashSet::new(),
                    },
                );
            }
            Stmt::Axiom(a) => {
                let direct_vars = OrderedVars::extract_with(&a.symbols, &frame.vars);
                let hypo_vars: OrderedVars = frame
                    .all_hypotheses
                    .iter()
                    .map(|h| &h.vars)
                    .fold(OrderedVars::default(), |acc, v| acc + v);

                let axiom_vars = hypo_vars + direct_vars;

                frame.ops.insert(
                    Label::from(a.name),
                    Unify {
                        vars: axiom_vars,
                        type_code: frame.resolve_symbol(a.type_code)?,
                        symbols: frame.resolve_symbols(a.symbols)?,
                        hypotheses: scope_stack.hypotheses(),
                        disjoints: scope_stack.disjoints(),
                    },
                );
            }

            Stmt::LogicalHypothesis(h) => {
                let hypothesis = Hypothesis {
                    label: Label::from(h.name),
                    type_code: frame.resolve_symbol(h.type_code)?,
                    vars: OrderedVars::extract_with(&h.symbols, &frame.vars),
                    symbols: frame.resolve_symbols(h.symbols)?,
                };

                scope_stack
                    .current_mut()
                    .hypotheses
                    .push(hypothesis.label.clone());

                frame.all_hypotheses.push(hypothesis);
            }

            Stmt::Theorem(t) => {
                let vars = OrderedVars::extract_with(&t.symbols, &frame.vars);
                let var_hypotheses = vars
                    .iter()
                    .map(|v| {
                        frame
                            .var_hypotheses
                            .get(v)
                            .ok_or_else(|| Error::NoVariableType(v.to_string()))
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let hypotheses = var_hypotheses
                    .into_iter()
                    .cloned()
                    .chain(scope_stack.hypotheses())
                    .collect();

                frame.theorems.push(Theorem {
                    name: Label::from(t.name),
                    type_code: frame.resolve_symbol(t.type_code)?,
                    symbols: frame.resolve_symbols(t.symbols)?,
                    proof: t.proof,
                    hypotheses,
                });
            }

            Stmt::Disjoint(_syms) => {
                scope_stack
                    .current_mut()
                    .disjoints
                    .extend(Disjoint::pairwise(&frame.resolve_symbols(_syms)?));
            }
        }
    }

    scope_stack.pop();

    Ok(())
}

#[derive(Default, Debug)]
struct Scope {
    hypotheses: Vec<Label>,
    disjoints: HashSet<Disjoint>,
}

trait VecScope {
    fn hypotheses(&self) -> Vec<Label>;
    fn disjoints(&self) -> HashSet<Disjoint>;
    fn current_mut(&mut self) -> &mut Scope;
}

impl VecScope for Vec<Scope> {
    fn hypotheses(&self) -> Vec<Label> {
        self.iter().flat_map(|s| &s.hypotheses).cloned().collect()
    }

    fn disjoints(&self) -> HashSet<Disjoint> {
        self.iter().flat_map(|s| &s.disjoints).cloned().collect()
    }

    fn current_mut(&mut self) -> &mut Scope {
        self.last_mut().unwrap()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Disjoint(Symbol, Symbol);

impl Disjoint {
    fn pairwise(syms: &[Symbol]) -> impl Iterator<Item = Disjoint> + '_ {
        syms.iter().flat_map(move |outer| {
            syms.iter()
                .filter_map(move |inner| Disjoint::try_from((outer, inner)).ok())
        })
    }

    fn check_replacements(&self, r: &HashMap<Symbol, Vec<Symbol>>) -> Result<(), Error> {
        match (r.get(&self.0), r.get(&self.1)) {
            (Some(a), Some(b)) if a == b => Err(Error::OverlappingDisjoint),

            _ => Ok(()),
        }
    }
}

impl TryFrom<(&Symbol, &Symbol)> for Disjoint {
    type Error = Error;

    fn try_from((a, b): (&Symbol, &Symbol)) -> Result<Self, Self::Error> {
        match a.cmp(b) {
            std::cmp::Ordering::Less => Ok(Disjoint(a.clone(), b.clone())),
            std::cmp::Ordering::Equal => Err(Error::SelfDisjoint(a.to_string())),
            std::cmp::Ordering::Greater => Ok(Disjoint(b.clone(), a.clone())),
        }
    }
}

#[derive(Default, Debug, PartialEq, Eq)]
struct Frame {
    vars: HashSet<Symbol>,
    consts: HashSet<Symbol>,

    all_hypotheses: Vec<Hypothesis>,
    var_hypotheses: HashMap<Symbol, Label>,

    theorems: Vec<Theorem>,
    ops: HashMap<Label, Unify>,
}

impl Frame {
    fn resolve_symbols(&self, symbols: Vec<String>) -> Result<Vec<Symbol>, Error> {
        symbols
            .into_iter()
            .map(|s| self.resolve_symbol(s))
            .collect()
    }

    fn resolve_symbol(&self, s: impl AsRef<str>) -> Result<Symbol, Error> {
        let as_symbol = Symbol::from(s.as_ref().to_string());
        None.or_else(|| self.vars.get(&as_symbol))
            .or_else(|| self.consts.get(&as_symbol))
            .cloned()
            .ok_or_else(|| Error::UnrecognizedSymbol(as_symbol.to_string()))
    }

    fn get_op(&self, label: &str) -> Option<&Unify> {
        self.ops.get(&Label::from(label.to_string()))
    }

    fn get_hypothesis(&self, label: &str) -> Option<&Hypothesis> {
        self.all_hypotheses.iter().find(|h| *h.label == label)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Unify {
    vars: OrderedVars,
    type_code: Symbol,
    symbols: Vec<Symbol>,

    // TODO(shelbyd): Should be Vec<Rc<Hypothesis>>.
    hypotheses: Vec<Label>,
    disjoints: HashSet<Disjoint>,
}

impl Unify {
    fn apply_to(
        &self,
        stack: &mut Vec<Sequence>,
        all_hypotheses: &Vec<Hypothesis>,
    ) -> Result<(), Error> {
        let hypotheses_proofs = self
            .hypotheses
            .iter()
            .rev()
            .map(|h| {
                let statement = stack
                    .pop()
                    .ok_or_else(|| Error::ExhaustedStack(h.to_string()))?;
                Ok((h, statement))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let mut replacements = HashMap::new();

        for var in self.vars.rev_iter() {
            // TODO(shelbyd): Check typeclass.
            let top = stack
                .pop()
                .ok_or_else(|| Error::ExhaustedStack(var.to_string()))?;
            replacements.insert(var.clone(), top.symbols);
        }

        for disjoint in &self.disjoints {
            disjoint.check_replacements(&replacements)?;
        }

        for (hypothesis, provided) in hypotheses_proofs {
            let hypothesis = all_hypotheses
                .iter()
                .find(|h| h.label == *hypothesis)
                .unwrap();

            let expected = Sequence {
                type_code: hypothesis.type_code.clone(),
                symbols: replace(&hypothesis.symbols, &replacements),
            };

            if expected != provided {
                return Err(Error::MismatchedStep {
                    expected: expected.to_string(),
                    got: provided.to_string(),
                });
            }
        }

        stack.push(Sequence {
            type_code: self.type_code.clone(),
            symbols: replace(&self.symbols, &replacements),
        });
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Hypothesis {
    label: Label,
    vars: OrderedVars,

    // TODO(shelbyd): Should be Sequence?
    type_code: Symbol,
    symbols: Vec<Symbol>,
}

#[derive(Debug, PartialEq, Eq)]
struct Theorem {
    name: Label,
    type_code: Symbol,
    symbols: Vec<Symbol>,
    proof: Proof,
    hypotheses: Vec<Label>,
}

#[derive(PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
struct Symbol(Rc<String>);

impl Deref for Symbol {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl From<String> for Symbol {
    fn from(s: String) -> Self {
        Symbol(Rc::new(s))
    }
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (**self).fmt(f)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct Label(Rc<String>);

impl Deref for Label {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl From<String> for Label {
    fn from(s: String) -> Self {
        Label(Rc::new(s))
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
struct Sequence {
    type_code: Symbol,
    symbols: Vec<Symbol>,
}

impl Sequence {
    fn to_string(&self) -> String {
        let mut result = self.type_code.to_string();

        for sym in &self.symbols {
            result += " ";
            result += sym;
        }

        result
    }
}

impl std::fmt::Debug for Sequence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

fn replace(syms: &[Symbol], replacements: &HashMap<Symbol, Vec<Symbol>>) -> Vec<Symbol> {
    syms.iter()
        .flat_map(|s| {
            replacements
                .get(s)
                .cloned()
                .unwrap_or_else(|| vec![s.clone()])
        })
        .collect::<Vec<_>>()
}

#[derive(Debug, PartialEq, Eq, Default, Clone)]
struct OrderedVars {
    vars: Vec<Symbol>,
}

impl OrderedVars {
    fn extract_with(syms: &[impl AsRef<str>], vars: &HashSet<Symbol>) -> Self {
        OrderedVars {
            vars: syms
                .iter()
                .map(|s| s.as_ref())
                .filter_map(|s| vars.get(&Symbol::from(s.to_string())).cloned())
                .unique() // TODO(shelbyd): Test that requires unique
                .collect(),
        }
    }

    fn rev_iter(&self) -> impl Iterator<Item = &Symbol> {
        self.vars.iter().rev()
    }

    fn iter(&self) -> impl Iterator<Item = &Symbol> {
        self.vars.iter()
    }
}

impl<O> core::ops::Add<O> for OrderedVars
where
    O: core::borrow::Borrow<OrderedVars>,
{
    type Output = OrderedVars;

    fn add(mut self, rhs: O) -> Self::Output {
        for var in &rhs.borrow().vars {
            if !self.vars.contains(&var) {
                self.vars.push(var.clone());
            }
        }
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::parse;

    #[test]
    fn empty_file() {
        assert_eq!(verify(vec![]), Ok(()));
    }

    #[test]
    fn empty_proof() {
        let file = "
            $c term $.
            $v t $. 
            tt $f term t $. 
            the1 $p term t $= $.
        ";

        assert_eq!(
            verify(parse(file).unwrap()),
            Err(Error::MismatchedStack("the1".to_string()))
        );
    }

    #[test]
    fn minimal_proof() {
        let file = "
            $c term $.
            $v t $.
            tt $f term t $.
            
            the1 $p term t $= tt $.
        ";

        assert_eq!(verify(parse(file).unwrap()), Ok(()));
    }

    #[test]
    fn undefined_step() {
        let file = "
            $c term $.
            $v t $.

            tt $f term t $.
            
            the1 $p term t $= missing $.
        ";

        assert_eq!(
            verify(parse(file).unwrap()),
            Err(Error::UnrecognizedLabel("missing".to_string()))
        );
    }

    #[test]
    fn type_setting_axiom() {
        let file = "
            $c 0 term $.
            tze $a term 0 $.
            
            the1 $p term 0 $= tze $.
        ";

        assert_eq!(verify(parse(file).unwrap()), Ok(()));
    }

    #[test]
    fn axiom_in_block() {
        let file = "
            $c 0 term $.
            ${
                tze $a term 0 $.
            $}
            
            the1 $p term 0 $= tze $.
        ";

        assert_eq!(verify(parse(file).unwrap()), Ok(()));
    }

    #[test]
    fn variable_in_axiom() {
        let file = "
            $c num happy 0 $.
            $v n $.

            num_n $f num n $.

            num_zero $a num 0 $.
            num_happy $a happy n $.
            
            the1 $p happy 0 $= num_zero num_happy $.
        ";

        assert_eq!(verify(parse(file).unwrap()), Ok(()));
    }

    #[test]
    fn only_replaces_once() {
        let file = "
            $c num 0 = true $.
            $v n $.

            num_n $f num n $.

            num_zero $a num 0 $.
            num_eq_self $a true n = n $.
            
            the1 $p true 0 = 0 $= num_zero num_eq_self $.
        ";

        assert_eq!(verify(parse(file).unwrap()), Ok(()));
    }

    #[test]
    fn num_happy_as_nested() {
        let file = "
            $c true num happy 0 1 > $.
            $v n $.

            num_n $f num n $.
            num_one $a num 1 $.

            one_gt_zero $a true 1 > 0 $.

            ${
                is_gt_ze $e true n > 0 $.
                num_happy $a happy n $.
            $}
            
            the1 $p happy 1 $= num_one one_gt_zero num_happy $.
        ";

        assert_eq!(verify(parse(file).unwrap()), Ok(()));
    }

    #[test]
    fn incorrect_statement_in_hypothesis() {
        let file = "
            $c true num happy 0 1 > $.
            $v n $.

            num_n $f num n $.
            num_zero $a num 0 $.

            one_gt_zero $a true 1 > 0 $.

            ${
                is_gt_ze $e true n > 0 $.
                num_happy $a happy n $.
            $}
            
            the1 $p happy 0 $= num_zero one_gt_zero num_happy $.
        ";

        assert_eq!(
            verify(parse(file).unwrap()),
            Err(Error::MismatchedStep {
                expected: String::from("true 0 > 0"),
                got: String::from("true 1 > 0"),
            })
        );
    }

    #[test]
    fn happy_with_two_vars() {
        let file = "
            $c true num happy 0 1 > < $.
            $v n m $.

            num_n $f num n $.
            num_m $f num m $.
            num_zero $a num 0 $.
            num_one  $a num 1 $.

            zero_lt_one $a true 0 < 1 $.

            ${
                is_gt $e true m < n $.
                num_happy $a happy n $.
            $}
            
            the1 $p happy 1 $= num_zero num_one zero_lt_one num_happy $.
        ";

        assert_eq!(verify(parse(file).unwrap()), Ok(()));
    }

    #[test]
    fn allows_empty_sequence() {
        let file = "
            $c wff M $.
            $v x $.

            wx $f wff x $.

            we $a wff $. 
            wM $a wff x M $.

            the1 $p wff M $= we wM $.
        ";

        assert_eq!(verify(parse(file).unwrap()), Ok(()));
    }

    #[test]
    // #[ignore]
    fn theroem_using_hypothesis() {
        let file = "
            $c |- |= term $.
            $v A R $.

            ta $f term A $.
            tr $f term R $.

            ${
              idi.1 $e |- R |= A $.
              idi $p |- R |= A $=
                (  ) C $.
            $}
        ";

        assert_eq!(verify(parse(file).unwrap()), Ok(()));
    }

    mod compressed {
        use super::*;

        #[test]
        fn single_step() {
            let file = "
                $c term $.
                $v t $.
                tt $f term t $.
            
                the1 $p term t $= ( tt ) A $.
            ";

            assert_eq!(verify(parse(file).unwrap()), Ok(()));
        }

        #[test]
        fn does_not_provide_other_frame_hypotheses() {
            let file = "
                $c term $.
                $v t $.
                tt $f term t $.

                ${
                    should_not_be_used $e term t $.
                    axiom $a term t $.
                $}
            
                the1 $p term t $= ( tt ) A $.
            ";

            assert_eq!(verify(parse(file).unwrap()), Ok(()));
        }

        #[test]
        fn demo0_compressed() {
            let file = include_str!("./db/demo0_compressed.mm");

            assert_eq!(verify(parse(file).unwrap()), Ok(()));
        }
    }

    mod compilation {
        use super::*;

        #[test]
        fn does_not_require_from_other_frames() {
            let file = "
                $c true num happy sad 0 1 > = $.
                $v n $.

                num_n $f num n $.
                num_one $a num 1 $.

                one_gt_zero $a true 1 > 0 $.

                ${
                    is_eq_ze $e true n = 0 $.
                    num_sad $a sad n $.
                $}

                ${
                    is_gt_ze $e true n > 0 $.
                    num_happy $a happy n $.
                $}
            
                the1 $p happy 1 $= num_one one_gt_zero num_happy $.
            ";

            let frame = compile(parse(file).unwrap()).unwrap();
            assert_eq!(
                frame.get_op("num_happy").unwrap().hypotheses,
                vec![Label::from("is_gt_ze".to_string())]
            );
        }

        #[test]
        fn undefined_symbol() {
            let file = "
                $c |- ( ) $.

                ${
                  foo $e |- ( ph -> -. ps ) $.
                  axiom $p |- ( ph -> ( ps -> ch ) ) $=
                    ( wn ) ACBABECEDFG $.
                $}
            ";

            assert_eq!(
                compile(parse(file).unwrap()),
                Err(Error::UnrecognizedSymbol("ph".to_string()))
            );
        }

        #[test]
        fn hypotheses_from_theorem_statement() {
            let file = "
                $c term $.
                $v t $.

                tt $f term t $.

                the1 $p term t $= ( ) A $.
            ";

            let frame = compile(parse(file).unwrap()).unwrap();
            assert_eq!(
                frame.theorems[0].hypotheses,
                vec![Label::from("tt".to_string())]
            );
        }
    }

    mod disjoint {
        use super::*;

        #[test]
        fn x_ne_y() {
            let file = "
                $c true num 0 1 != $.
                $v x y $.

                num_x $f num x $.
                num_y $f num y $.

                num_zero $a num 0 $.
                num_one  $a num 1 $.

                ${
                    $d x y $.
                    x_ne_y $a true x != y $.
                $}
            
                the1 $p true 0 != 1 $= num_zero num_one x_ne_y $.
            ";

            assert_eq!(verify(parse(file).unwrap()), Ok(()));
        }

        #[test]
        fn try_to_provide_same_value() {
            let file = "
                $c true num 0 1 != $.
                $v x y $.

                num_x $f num x $.
                num_y $f num y $.

                num_zero $a num 0 $.
                num_one  $a num 1 $.

                ${
                    $d x y $.
                    x_ne_y $a true x != y $.
                $}
            
                the1 $p true 0 != 0 $= num_zero num_zero x_ne_y $.
            ";

            assert_eq!(
                verify(parse(file).unwrap()),
                Err(Error::OverlappingDisjoint)
            );
        }

        // TODO(shelbyd): Using same variable.
    }
}
