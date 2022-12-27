use itertools::*;
use std::collections::{HashMap, HashSet};

use crate::ast::Stmt;

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
    // let mut consts = Vec::new();
    let mut vars = HashSet::new();
    let mut all_hypotheses = Vec::<Hypothesis>::new();

    let mut ops = HashMap::new();

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
                    Operation::PushExact(format!("{} {}", f.type_code, f.var)),
                );
            }
            Stmt::Axiom(a) => {
                let direct_vars = a.symbols.iter().filter(|s| vars.contains(*s));
                let hypo_vars = all_hypotheses.iter().flat_map(|h| &h.vars);

                let vars = std::iter::empty()
                    .chain(hypo_vars)
                    .chain(direct_vars)
                    .unique()
                    .cloned()
                    .collect();

                ops.insert(
                    a.name,
                    Operation::Unify {
                        vars,
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
                    vars: h
                        .symbols
                        .iter()
                        .filter(|s| vars.contains(*s))
                        .unique()
                        .cloned()
                        .collect(),
                    symbols: h.symbols,
                });
            }

            Stmt::Proof(p) => {
                let target = format!("{} {}", p.type_code, p.symbols.join(" "));

                let mut stack = Vec::<String>::new();
                for step in p.proof {
                    let labeled = ops.get(&step).ok_or(Error::UnrecognizedLabel(step))?;
                    match labeled {
                        Operation::PushExact(s) => stack.push(s.clone()),

                        Operation::Unify {
                            vars,
                            type_code,
                            symbols,
                            hypotheses,
                        } => {
                            let mut replacements = HashMap::<String, String>::new();

                            let hypotheses_proofs = hypotheses
                                .iter()
                                .rev()
                                .map(|h| {
                                    let statement = stack
                                        .pop()
                                        .ok_or_else(|| Error::ExhaustedStack(h.to_string()))?;
                                    Ok((h, statement))
                                })
                                .collect::<Result<Vec<_>, _>>()?;

                            for var in vars.iter().rev() {
                                // TODO(shelbyd): Check typeclass.
                                let top = stack
                                    .pop()
                                    .ok_or_else(|| Error::ExhaustedStack(var.to_string()))?;
                                let suff = top.split_once(" ").unwrap().1;
                                replacements.insert(var.to_string(), suff.to_string());
                            }

                            for (hypothesis, statement) in hypotheses_proofs {
                                let hypothesis = all_hypotheses
                                    .iter()
                                    .find(|h| h.label == *hypothesis)
                                    .unwrap();
                                let replaced = hypothesis
                                    .symbols
                                    .iter()
                                    .map(|s| replacements.get(s).unwrap_or(s).as_str())
                                    .collect::<Vec<_>>();
                                let expected =
                                    format!("{} {}", hypothesis.type_code, replaced.join(" "));
                                if expected != statement {
                                    return Err(Error::MismatchedStep {
                                        expected,
                                        got: statement,
                                    });
                                }
                            }

                            let replaced = symbols
                                .iter()
                                .map(|s| replacements.get(s).unwrap_or(s).as_str())
                                .collect::<Vec<_>>();
                            stack.push(format!("{type_code} {}", replaced.join(" ")));
                        }
                    }
                }

                if stack != vec![target] {
                    dbg!(&stack);
                    return Err(Error::MismatchedStack(p.name));
                }
            }

            _ => {
                dbg!(stmt);
            }
        }
    }
    Ok(())
}

#[derive(Debug)]
enum Operation {
    PushExact(String),

    Unify {
        vars: Vec<String>,
        type_code: String,
        symbols: Vec<String>,
        hypotheses: Vec<String>,
    },
}

#[derive(Debug)]
struct Hypothesis {
    label: String,
    type_code: String,
    symbols: Vec<String>,
    vars: Vec<String>,
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
}
