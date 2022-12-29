use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet},
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
                    frame
                        .get_op(step)?
                        .apply_to(&mut stack, &frame.all_hypotheses)?;
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
    hypotheses_stack: &mut Vec<Vec<Label>>,
) -> Result<(), Error> {
    hypotheses_stack.push(Vec::new());

    for stmt in stmts {
        match stmt {
            Stmt::ConstantDecl(c) => frame.consts.extend(c.into_iter().map(Symbol::from)),
            Stmt::VarDecl(v) => frame.vars.extend(v.into_iter().map(Symbol::from)),

            Stmt::Block(b) => {
                compile_into(b, frame, hypotheses_stack)?;
            }

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
                        hypotheses: hypotheses_stack.iter().flat_map(|v| v).cloned().collect(),
                    },
                );
            }

            Stmt::LogicalHypothesis(h) => {
                let label = Label::from(h.name);
                hypotheses_stack.last_mut().unwrap().push(label.clone());

                frame.all_hypotheses.push(Hypothesis {
                    label,
                    type_code: frame.resolve_symbol(h.type_code)?,
                    vars: OrderedVars::extract_with(&h.symbols, &frame.vars),
                    symbols: frame.resolve_symbols(h.symbols)?,
                });
            }

            Stmt::Theorem(t) => {
                let vars = OrderedVars::extract_with(&t.symbols, &frame.vars);
                let var_hypotheses = vars.iter().map(|v| frame.var_hypotheses.get(v).unwrap());

                let hypotheses = var_hypotheses
                    .chain(hypotheses_stack.iter().flat_map(|v| v))
                    .cloned()
                    .collect();

                frame.theorems.push(Theorem {
                    name: Label::from(t.name),
                    type_code: frame.resolve_symbol(t.type_code)?,
                    symbols: frame.resolve_symbols(t.symbols)?,
                    proof: t.proof,
                    hypotheses,
                });
            }

            _ => todo!("{stmt:?}"),
        }
    }

    hypotheses_stack.pop();

    Ok(())
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

    fn get_op(&self, step: &str) -> Result<&Unify, Error> {
        self.ops
            .get(&Label::from(step.to_string()))
            .ok_or(Error::UnrecognizedLabel(step.to_string()))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Unify {
    vars: OrderedVars,
    type_code: Symbol,
    symbols: Vec<Symbol>,

    // TODO(shelbyd): Should be Vec<Rc<Hypothesis>>.
    hypotheses: Vec<Label>,
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
    type_code: Symbol,
    symbols: Vec<Symbol>,
    vars: OrderedVars,
}

#[derive(Debug, PartialEq, Eq)]
struct Theorem {
    name: Label,
    type_code: Symbol,
    symbols: Vec<Symbol>,
    proof: Proof,
    hypotheses: Vec<Label>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
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
}
