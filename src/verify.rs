use std::collections::{HashMap, HashSet};

use crate::ast::Stmt;

pub fn verify(stmts: Vec<Stmt>) -> anyhow::Result<()> {
    Verifier::new().verify_block(stmts)
}

type TypeClass = String;
type Con = String;
type Var = String;
type Lab = String;
type Sym = String; // (Con || Var)

#[derive(Default, Debug)]
struct Verifier {
    consts: HashSet<Con>,

    vars: HashSet<Var>,

    type_classes: HashMap<Var, TypeClass>,
    type_class_defs: HashMap<Lab, (TypeClass, Var)>,

    theorems: HashMap<Lab, Theorem>,
}

#[derive(Debug)]
struct Theorem {
    type_class: TypeClass,
    symbols: Vec<Sym>,
}

impl Verifier {
    fn new() -> Self {
        Default::default()
    }

    fn verify(&mut self, stmt: Stmt) -> anyhow::Result<()> {
        match stmt {
            Stmt::ConstantDecl(consts) => {
                self.consts.extend(consts);
            }
            Stmt::VarDecl(vars) => {
                self.vars.extend(vars);
            }

            Stmt::FloatingHypothesis(h) => {
                self.type_classes.insert(h.var.clone(), h.type_code.clone());
                self.type_class_defs.insert(h.name, (h.type_code, h.var));
            }
            Stmt::LogicalHypothesis(_expr) => {
                dbg!(_expr);
            }

            Stmt::Axiom(a) => {
                self.theorems.insert(
                    a.name,
                    Theorem {
                        type_class: a.type_code,
                        symbols: a.symbols,
                    },
                );
            }
            Stmt::Block(b) => self.verify_block(b)?,

            Stmt::Proof(p) => {
                let reduced = self.reduce(p.proof)?;
                unimplemented!("{:?}", reduced);
            }

            u => {
                unimplemented!("{:?}", u);
            }
        }

        Ok(())
    }

    fn verify_block(&mut self, block: Vec<Stmt>) -> anyhow::Result<()> {
        for stmt in block {
            self.verify(stmt)?;
        }
        Ok(())
    }

    fn reduce(&self, syms: Vec<Sym>) -> anyhow::Result<Vec<Sym>> {
        let mut stack = Vec::new();

        for sym in syms {
            dbg!(&stack, &sym);

            if let Some((type_class, var)) = self.type_class_defs.get(&sym) {
                stack.push(format!("{type_class} {var}"));
                continue;
            }

            if let Some(theorem) = self.theorems.get(&sym) {
                let vars = theorem
                    .symbols
                    .iter()
                    .filter_map(|s| self.vars.get(s))
                    .rev()
                    .collect::<Vec<_>>();

                let mut replacements = HashMap::new();
                for var in vars {
                    if let Some(_) = replacements.get(var) {
                        continue;
                    }

                    let top = stack.pop().ok_or(anyhow::anyhow!("Stack exhausted"))?;
                    let expected_class = self
                        .type_classes
                        .get(var)
                        .ok_or(anyhow::anyhow!("Unrecognized variable: {var:?}"))?;

                    let replacement =
                        top.strip_prefix(&format!("{expected_class} "))
                            .ok_or(anyhow::anyhow!(
                                "Expected type_class {expected_class:?}, found {top:?}"
                            ))?;
                    replacements.insert(var, replacement.to_string());
                }

                let replaced = theorem
                    .symbols
                    .iter()
                    .map(|s| replacements.get(s).unwrap_or(s).as_str())
                    .collect::<Vec<_>>()
                    .join(" ");

                stack.push(format!("{} {replaced}", theorem.type_class));
                continue;
            }

            anyhow::bail!("Unrecognized symbol: {sym}");
        }

        Ok(stack)
    }
}
