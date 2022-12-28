use itertools::Itertools;
use std::collections::{HashMap, HashSet};

use crate::{ast::Stmt, proof::Step};

#[derive(thiserror::Error, Debug, PartialEq, Eq)]
pub enum Error {
    #[error("mismatched final stack for: {0}")]
    MismatchedStack(String),

    #[error("unrecognized label: {0}")]
    UnrecognizedLabel(String),

    #[error("exhausted stack trying to resolve: {0}")]
    ExhaustedStack(String),

    #[error("mismatched step, expected \n  {expected}\ngot \n  {got}")]
    MismatchedStep { expected: String, got: String },
}

pub fn verify(stmts: Vec<Stmt>) -> Result<(), Error> {
    let mut vars = HashSet::new();
    let mut all_hypotheses = Vec::<Hypothesis>::new();

    let mut ops = HashMap::new();

    // TODO(shelbyd): Don't flatten.
    let flattened = stmts.into_iter().flat_map(|s| match s {
        Stmt::Block(b) => b,
        _ => vec![s],
    });
    for stmt in flattened {
        match stmt {
            Stmt::ConstantDecl(_) => {}
            Stmt::VarDecl(v) => vars.extend(v),

            Stmt::VarTypeDecl(f) => {
                // TODO(shelbyd): Check var is a var.
                ops.insert(
                    f.name,
                    Unify {
                        vars: OrderedVars::default(),
                        type_code: f.type_code,
                        symbols: vec![f.var],
                        hypotheses: vec![],
                    },
                );
            }
            Stmt::Axiom(a) => {
                let direct_vars = OrderedVars::extract_with(&a.symbols, &vars);
                let hypo_vars: OrderedVars = all_hypotheses
                    .iter()
                    .map(|h| &h.vars)
                    .fold(OrderedVars::default(), |acc, v| acc + v);

                let axiom_vars = hypo_vars + direct_vars;

                ops.insert(
                    a.name,
                    Unify {
                        vars: axiom_vars,
                        type_code: a.type_code,
                        symbols: a.symbols,
                        hypotheses: all_hypotheses.iter().map(|h| h.label.clone()).collect(),
                    },
                );
            }

            Stmt::LogicalHypothesis(h) => {
                all_hypotheses.push(Hypothesis {
                    label: h.name,
                    type_code: h.type_code,
                    vars: OrderedVars::extract_with(&h.symbols, &vars),
                    symbols: h.symbols,
                });
            }

            Stmt::Theorem(p) => {
                let mut stack = Vec::new();
                let mut heap = Vec::<String>::new();

                // TODO(shelbyd): Provide this correctly / Unit tests for this.
                let mandatory_hypotheses = all_hypotheses
                    .iter()
                    .map(|h| h.label.as_str())
                    .collect::<Vec<_>>();
                for step in p.proof.plain(&mandatory_hypotheses) {
                    match step {
                        Step::Label(step) => {
                            ops.get(step)
                                .ok_or(Error::UnrecognizedLabel(step.to_string()))?
                                .apply_to(&mut stack, &all_hypotheses)?;
                        }
                        Step::ToHeap => {
                            heap.push(stack.last().unwrap().clone());
                        }
                    }
                }

                let target = statement(&p.type_code, p.symbols);
                if stack != vec![target] {
                    dbg!(&stack);
                    return Err(Error::MismatchedStack(p.name));
                }
            }

            _ => todo!("{stmt:?}"),
        }
    }
    Ok(())
}

#[derive(Debug, Clone)]
struct Unify {
    vars: OrderedVars,
    type_code: String,
    symbols: Vec<String>,
    hypotheses: Vec<String>,
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

        let mut replacements = HashMap::<String, String>::new();

        for var in self.vars.rev_iter() {
            // TODO(shelbyd): Check typeclass.
            let top = stack
                .pop()
                .ok_or_else(|| Error::ExhaustedStack(var.to_string()))?;
            let suff = top.split_once(" ").unwrap().1;
            replacements.insert(var.to_string(), suff.to_string());
        }

        for (hypothesis, provided) in hypotheses_proofs {
            let hypothesis = all_hypotheses
                .iter()
                .find(|h| h.label == *hypothesis)
                .unwrap();

            let expected = statement(
                &hypothesis.type_code,
                replace(&hypothesis.symbols, &replacements),
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
            replace(&self.symbols, &replacements),
        ));
        Ok(())
    }
}

#[derive(Debug)]
struct Hypothesis {
    label: String,
    type_code: String,
    symbols: Vec<String>,
    vars: OrderedVars,
}

fn replace(syms: &[impl AsRef<str>], replacements: &HashMap<String, String>) -> Vec<String> {
    syms.iter()
        .map(|s| s.as_ref())
        .map(|s| {
            replacements
                .get(s)
                .cloned()
                .unwrap_or_else(|| s.to_string())
        })
        .collect::<Vec<_>>()
}

fn statement(type_code: &str, replacements: Vec<String>) -> String {
    format!("{type_code} {}", replacements.join(" "))
}

#[derive(Debug, PartialEq, Eq, Default, Clone)]
struct OrderedVars {
    vars: Vec<String>,
}

impl OrderedVars {
    fn extract_with(syms: &[impl AsRef<str>], vars: &HashSet<String>) -> Self {
        OrderedVars {
            vars: syms
                .iter()
                .map(|s| s.as_ref())
                .filter(|s| vars.contains(*s))
                .unique() // TODO(shelbyd): Test that requires unique
                .map(|s| s.to_string())
                .collect(),
        }
    }

    fn rev_iter(&self) -> impl Iterator<Item = &str> {
        self.vars.iter().rev().map(|s| s.as_str())
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
                self.vars.push(var.to_string());
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
            verify(parse("the1 $p t $= $.").unwrap()),
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
            $c num happy 0 1 > $.
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
            $c num happy 0 1 > $.
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
            $c num happy 0 1 > $.
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
    #[ignore]
    fn does_not_require_from_other_frames() {
        let file = "
            $c num happy sad 0 1 > = $.
            $v n $.

            num_n $f num n $.
            num_one $a num 1 $.

            one_gt_zero $a true 1 > 0 $.

            ${
                is_gt_ze $e true n = 0 $.
                num_sad $a sad n $.
            $}

            ${
                is_gt_ze $e true n > 0 $.
                num_happy $a happy n $.
            $}
            
            the1 $p happy 1 $= num_one one_gt_zero num_happy $.
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
}
