use std::fmt;

use serde::{Deserialize, Serialize};

pub type Lit = i32;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CnfFormula {
    pub num_vars: u32,
    pub clauses: Vec<Vec<Lit>>,
}

impl CnfFormula {
    pub fn to_dimacs(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("p cnf {} {}\n", self.num_vars, self.clauses.len()));
        for clause in &self.clauses {
            for lit in clause {
                out.push_str(&lit.to_string());
                out.push(' ');
            }
            out.push_str("0\n");
        }
        out
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CnfBuilder {
    next_var: Lit,
    clauses: Vec<Vec<Lit>>,
    true_lit: Lit,
}

impl Default for CnfBuilder {
    fn default() -> Self {
        let mut builder = Self {
            next_var: 0,
            clauses: Vec::new(),
            true_lit: 0,
        };
        let true_lit = builder.fresh_lit();
        builder.add_unit(true_lit);
        builder.true_lit = true_lit;
        builder
    }
}

impl CnfBuilder {
    fn is_const_true(&self, lit: Lit) -> bool {
        lit == self.true_lit
    }

    fn is_const_false(&self, lit: Lit) -> bool {
        lit == -self.true_lit
    }

    pub fn finish(self) -> CnfFormula {
        CnfFormula {
            num_vars: self.next_var as u32,
            clauses: self.clauses,
        }
    }

    pub fn fresh_lit(&mut self) -> Lit {
        self.next_var += 1;
        self.next_var
    }

    pub fn const_true(&self) -> Lit {
        self.true_lit
    }

    pub fn const_false(&self) -> Lit {
        -self.true_lit
    }

    pub fn const_bitvec(&self, width: u32, value: u64) -> Vec<Lit> {
        (0..width)
            .map(|index| {
                if ((value >> index) & 1) == 1 {
                    self.const_true()
                } else {
                    self.const_false()
                }
            })
            .collect()
    }

    pub fn add_clause(&mut self, clause: impl Into<Vec<Lit>>) {
        self.clauses.push(clause.into());
    }

    pub fn add_unit(&mut self, lit: Lit) {
        self.add_clause(vec![lit]);
    }

    pub fn not(&self, lit: Lit) -> Lit {
        -lit
    }

    pub fn and(&mut self, lhs: Lit, rhs: Lit) -> Lit {
        if lhs == rhs {
            return lhs;
        }
        if lhs == -rhs {
            return self.const_false();
        }
        if self.is_const_false(lhs) || self.is_const_false(rhs) {
            return self.const_false();
        }
        if self.is_const_true(lhs) {
            return rhs;
        }
        if self.is_const_true(rhs) {
            return lhs;
        }

        let out = self.fresh_lit();
        self.add_clause(vec![-out, lhs]);
        self.add_clause(vec![-out, rhs]);
        self.add_clause(vec![out, -lhs, -rhs]);
        out
    }

    pub fn or(&mut self, lhs: Lit, rhs: Lit) -> Lit {
        if lhs == rhs {
            return lhs;
        }
        if lhs == -rhs {
            return self.const_true();
        }
        if self.is_const_true(lhs) || self.is_const_true(rhs) {
            return self.const_true();
        }
        if self.is_const_false(lhs) {
            return rhs;
        }
        if self.is_const_false(rhs) {
            return lhs;
        }

        let out = self.fresh_lit();
        self.add_clause(vec![out, -lhs]);
        self.add_clause(vec![out, -rhs]);
        self.add_clause(vec![-out, lhs, rhs]);
        out
    }

    pub fn xor(&mut self, lhs: Lit, rhs: Lit) -> Lit {
        if lhs == rhs {
            return self.const_false();
        }
        if lhs == -rhs {
            return self.const_true();
        }
        if self.is_const_false(lhs) {
            return rhs;
        }
        if self.is_const_false(rhs) {
            return lhs;
        }
        if self.is_const_true(lhs) {
            return self.not(rhs);
        }
        if self.is_const_true(rhs) {
            return self.not(lhs);
        }

        let out = self.fresh_lit();
        self.add_clause(vec![-lhs, -rhs, -out]);
        self.add_clause(vec![lhs, rhs, -out]);
        self.add_clause(vec![lhs, -rhs, out]);
        self.add_clause(vec![-lhs, rhs, out]);
        out
    }

    pub fn eq(&mut self, lhs: Lit, rhs: Lit) -> Lit {
        if lhs == rhs {
            self.const_true()
        } else if lhs == -rhs {
            self.const_false()
        } else {
            let xor = self.xor(lhs, rhs);
            self.not(xor)
        }
    }

    pub fn xor3(&mut self, a: Lit, b: Lit, c: Lit) -> Lit {
        if self.is_const_false(a) {
            return self.xor(b, c);
        }
        if self.is_const_false(b) {
            return self.xor(a, c);
        }
        if self.is_const_false(c) {
            return self.xor(a, b);
        }
        if self.is_const_true(a) {
            let parity = self.xor(b, c);
            return self.not(parity);
        }
        if self.is_const_true(b) {
            let parity = self.xor(a, c);
            return self.not(parity);
        }
        if self.is_const_true(c) {
            let parity = self.xor(a, b);
            return self.not(parity);
        }

        let out = self.fresh_lit();
        self.add_clause(vec![-a, -b, -c, -out]);
        self.add_clause(vec![-a, b, c, -out]);
        self.add_clause(vec![a, -b, c, -out]);
        self.add_clause(vec![a, b, -c, -out]);
        self.add_clause(vec![a, b, c, out]);
        self.add_clause(vec![a, -b, -c, out]);
        self.add_clause(vec![-a, b, -c, out]);
        self.add_clause(vec![-a, -b, c, out]);
        out
    }

    pub fn majority3(&mut self, a: Lit, b: Lit, c: Lit) -> Lit {
        if self.is_const_false(a) {
            return self.and(b, c);
        }
        if self.is_const_false(b) {
            return self.and(a, c);
        }
        if self.is_const_false(c) {
            return self.and(a, b);
        }
        if self.is_const_true(a) {
            return self.or(b, c);
        }
        if self.is_const_true(b) {
            return self.or(a, c);
        }
        if self.is_const_true(c) {
            return self.or(a, b);
        }

        let out = self.fresh_lit();
        self.add_clause(vec![-a, -b, out]);
        self.add_clause(vec![-a, -c, out]);
        self.add_clause(vec![-b, -c, out]);
        self.add_clause(vec![a, b, -out]);
        self.add_clause(vec![a, c, -out]);
        self.add_clause(vec![b, c, -out]);
        out
    }

    pub fn ite(&mut self, cond: Lit, then_lit: Lit, else_lit: Lit) -> Lit {
        if then_lit == else_lit {
            return then_lit;
        }
        if self.is_const_true(cond) {
            return then_lit;
        }
        if self.is_const_false(cond) {
            return else_lit;
        }
        if self.is_const_true(then_lit) && self.is_const_false(else_lit) {
            return cond;
        }
        if self.is_const_false(then_lit) && self.is_const_true(else_lit) {
            return self.not(cond);
        }
        if then_lit == self.not(else_lit) {
            return self.xor(cond, else_lit);
        }
        if else_lit == self.not(then_lit) {
            return self.xor(self.not(cond), then_lit);
        }

        let out = self.fresh_lit();
        self.add_clause(vec![-cond, -then_lit, out]);
        self.add_clause(vec![-cond, then_lit, -out]);
        self.add_clause(vec![cond, -else_lit, out]);
        self.add_clause(vec![cond, else_lit, -out]);
        out
    }

    pub fn or_all(&mut self, lits: impl IntoIterator<Item = Lit>) -> Lit {
        let mut normalized = Vec::new();
        for lit in lits {
            if self.is_const_true(lit) {
                return self.const_true();
            }
            if self.is_const_false(lit) {
                continue;
            }
            if normalized.iter().any(|existing| *existing == lit) {
                continue;
            }
            if normalized.iter().any(|existing| *existing == -lit) {
                return self.const_true();
            }
            normalized.push(lit);
        }

        let mut iter = normalized.into_iter();
        let Some(first) = iter.next() else {
            return self.const_false();
        };
        iter.fold(first, |acc, lit| self.or(acc, lit))
    }

    pub fn and_all(&mut self, lits: impl IntoIterator<Item = Lit>) -> Lit {
        let mut normalized = Vec::new();
        for lit in lits {
            if self.is_const_false(lit) {
                return self.const_false();
            }
            if self.is_const_true(lit) {
                continue;
            }
            if normalized.iter().any(|existing| *existing == lit) {
                continue;
            }
            if normalized.iter().any(|existing| *existing == -lit) {
                return self.const_false();
            }
            normalized.push(lit);
        }

        let mut iter = normalized.into_iter();
        let Some(first) = iter.next() else {
            return self.const_true();
        };
        iter.fold(first, |acc, lit| self.and(acc, lit))
    }
}

impl fmt::Display for CnfFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_dimacs())
    }
}
