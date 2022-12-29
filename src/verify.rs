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
        let mut stack = Vec::new();
        let mut heap = Vec::<String>::new();

        // TODO(shelbyd): Provide this correctly / Unit tests for this.
        let mandatory_hypotheses = frame
            .all_hypotheses
            .iter()
            .map(|h| h.label.as_str())
            .collect::<Vec<_>>();
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
            }
        }

        let target = statement(&frame.resolve_symbol(&t.type_code)?, &t.symbols);
        if stack != vec![target] {
            dbg!(&stack);
            return Err(Error::MismatchedStack(t.name.clone()));
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
                frame.ops.insert(
                    Label::from(f.name),
                    Unify {
                        vars: OrderedVars::default(),
                        type_code: frame.resolve_symbol(f.type_code)?,
                        symbols: frame.resolve_symbols(vec![f.var])?,
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

            Stmt::Theorem(p) => frame.theorems.push(p),

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
        stack: &mut Vec<String>,
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
            let suff = top.split_once(" ").unwrap().1;
            replacements.insert(var.clone(), suff.to_string());
        }

        for (hypothesis, provided) in hypotheses_proofs {
            let hypothesis = all_hypotheses
                .iter()
                .find(|h| h.label == *hypothesis)
                .unwrap();

            let expected = statement(
                &hypothesis.type_code,
                &replace(&hypothesis.symbols, &replacements),
            );

            if expected != provided {
                return Err(Error::MismatchedStep {
                    expected,
                    got: provided,
                });
            }
        }

        stack.push(statement(
            &self.type_code,
            &replace(&self.symbols, &replacements),
        ));
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

// TODO(shelbyd): Sequence of Symbols as type instead of String.

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

fn replace(syms: &[Symbol], replacements: &HashMap<Symbol, String>) -> Vec<String> {
    syms.iter()
        .map(|s| {
            replacements
                .get(s)
                .cloned()
                .unwrap_or_else(|| s.to_string())
        })
        .collect::<Vec<_>>()
}

fn statement(type_code: &Symbol, seq: &Vec<String>) -> String {
    format!("{} {}", **type_code, seq.join(" "))
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
        assert_eq!(
            verify(parse("$v t $. the1 $p t $= $.").unwrap()),
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
        #[ignore]
        fn proof_by_contradiction() {
            let file = include_str!("./proof_by_contradiction.mm");

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
    }
}
