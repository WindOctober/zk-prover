//! Minimal BTOR2 builder and serializer for the frontend lowering path.

use core::fmt;
use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

pub const CRATE_NAME: &str = "zkpv-btor2";

pub type NodeId = u64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnaryOp {
    Not,
    Neg,
}

impl UnaryOp {
    fn keyword(self) -> &'static str {
        match self {
            Self::Not => "not",
            Self::Neg => "neg",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    SDiv,
    UDiv,
    SRem,
    URem,
    And,
    Or,
    Xor,
    Eq,
    Slt,
    Slte,
    Sgt,
    Sgte,
    Ult,
    Ulte,
    Ugt,
    Ugte,
    Sll,
    Srl,
    Sra,
}

impl BinaryOp {
    fn keyword(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
            Self::SDiv => "sdiv",
            Self::UDiv => "udiv",
            Self::SRem => "srem",
            Self::URem => "urem",
            Self::And => "and",
            Self::Or => "or",
            Self::Xor => "xor",
            Self::Eq => "eq",
            Self::Slt => "slt",
            Self::Slte => "slte",
            Self::Sgt => "sgt",
            Self::Sgte => "sgte",
            Self::Ult => "ult",
            Self::Ulte => "ulte",
            Self::Ugt => "ugt",
            Self::Ugte => "ugte",
            Self::Sll => "sll",
            Self::Srl => "srl",
            Self::Sra => "sra",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Line {
    SortBitVec {
        id: NodeId,
        width: u32,
    },
    State {
        id: NodeId,
        sort: NodeId,
        symbol: String,
    },
    Input {
        id: NodeId,
        sort: NodeId,
        symbol: String,
    },
    Const {
        id: NodeId,
        sort: NodeId,
        value: String,
    },
    Unary {
        id: NodeId,
        op: UnaryOp,
        sort: NodeId,
        arg: NodeId,
    },
    Binary {
        id: NodeId,
        op: BinaryOp,
        sort: NodeId,
        lhs: NodeId,
        rhs: NodeId,
    },
    Ite {
        id: NodeId,
        sort: NodeId,
        cond: NodeId,
        then_value: NodeId,
        else_value: NodeId,
    },
    Slice {
        id: NodeId,
        sort: NodeId,
        value: NodeId,
        upper: u32,
        lower: u32,
    },
    Uext {
        id: NodeId,
        sort: NodeId,
        value: NodeId,
        amount: u32,
    },
    Sext {
        id: NodeId,
        sort: NodeId,
        value: NodeId,
        amount: u32,
    },
    Init {
        id: NodeId,
        sort: NodeId,
        state: NodeId,
        value: NodeId,
    },
    Next {
        id: NodeId,
        sort: NodeId,
        state: NodeId,
        value: NodeId,
    },
    Bad {
        id: NodeId,
        cond: NodeId,
        symbol: Option<String>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Program {
    pub lines: Vec<Line>,
}

impl Program {
    pub fn to_text(&self) -> String {
        let mut out = String::new();
        for line in &self.lines {
            use fmt::Write as _;
            let _ = writeln!(out, "{line}");
        }
        out
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, line) in self.lines.iter().enumerate() {
            if index > 0 {
                writeln!(f)?;
            }
            write!(f, "{line}")?;
        }
        Ok(())
    }
}

impl fmt::Display for Line {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SortBitVec { id, width } => write!(f, "{id} sort bitvec {width}"),
            Self::State { id, sort, symbol } => write!(f, "{id} state {sort} {symbol}"),
            Self::Input { id, sort, symbol } => write!(f, "{id} input {sort} {symbol}"),
            Self::Const { id, sort, value } => write!(f, "{id} constd {sort} {value}"),
            Self::Unary { id, op, sort, arg } => {
                write!(f, "{id} {} {sort} {arg}", op.keyword())
            }
            Self::Binary {
                id,
                op,
                sort,
                lhs,
                rhs,
            } => write!(f, "{id} {} {sort} {lhs} {rhs}", op.keyword()),
            Self::Ite {
                id,
                sort,
                cond,
                then_value,
                else_value,
            } => write!(f, "{id} ite {sort} {cond} {then_value} {else_value}"),
            Self::Slice {
                id,
                sort,
                value,
                upper,
                lower,
            } => write!(f, "{id} slice {sort} {value} {upper} {lower}"),
            Self::Uext {
                id,
                sort,
                value,
                amount,
            } => write!(f, "{id} uext {sort} {value} {amount}"),
            Self::Sext {
                id,
                sort,
                value,
                amount,
            } => write!(f, "{id} sext {sort} {value} {amount}"),
            Self::Init {
                id,
                sort,
                state,
                value,
            } => write!(f, "{id} init {sort} {state} {value}"),
            Self::Next {
                id,
                sort,
                state,
                value,
            } => write!(f, "{id} next {sort} {state} {value}"),
            Self::Bad { id, cond, symbol } => {
                if let Some(symbol) = symbol {
                    write!(f, "{id} bad {cond} {symbol}")
                } else {
                    write!(f, "{id} bad {cond}")
                }
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct Builder {
    next_id: NodeId,
    lines: Vec<Line>,
    sort_by_width: BTreeMap<u32, NodeId>,
    width_by_node: BTreeMap<NodeId, u32>,
}

impl Builder {
    pub fn new() -> Self {
        Self {
            next_id: 1,
            lines: Vec::new(),
            sort_by_width: BTreeMap::new(),
            width_by_node: BTreeMap::new(),
        }
    }

    pub fn finish(self) -> Program {
        Program { lines: self.lines }
    }

    pub fn bitvec_sort(&mut self, width: u32) -> NodeId {
        if let Some(id) = self.sort_by_width.get(&width) {
            return *id;
        }

        let id = self.alloc_id();
        self.lines.push(Line::SortBitVec { id, width });
        self.sort_by_width.insert(width, id);
        id
    }

    pub fn bool_sort(&mut self) -> NodeId {
        self.bitvec_sort(1)
    }

    pub fn width_of(&self, node: NodeId) -> u32 {
        *self
            .width_by_node
            .get(&node)
            .unwrap_or_else(|| panic!("missing width metadata for node {node}"))
    }

    pub fn state(&mut self, width: u32, symbol: impl Into<String>) -> NodeId {
        let sort = self.bitvec_sort(width);
        let id = self.alloc_value(width);
        self.lines.push(Line::State {
            id,
            sort,
            symbol: symbol.into(),
        });
        id
    }

    pub fn input(&mut self, width: u32, symbol: impl Into<String>) -> NodeId {
        let sort = self.bitvec_sort(width);
        let id = self.alloc_value(width);
        self.lines.push(Line::Input {
            id,
            sort,
            symbol: symbol.into(),
        });
        id
    }

    pub fn const_u64(&mut self, width: u32, value: u64) -> NodeId {
        let sort = self.bitvec_sort(width);
        let id = self.alloc_value(width);
        let normalized = normalize_to_width(value as u128, width);
        self.lines.push(Line::Const {
            id,
            sort,
            value: normalized.to_string(),
        });
        id
    }

    pub fn zero(&mut self, width: u32) -> NodeId {
        self.const_u64(width, 0)
    }

    pub fn one(&mut self, width: u32) -> NodeId {
        self.const_u64(width, 1)
    }

    pub fn unary(&mut self, op: UnaryOp, arg: NodeId) -> NodeId {
        let width = self.width_of(arg);
        let sort = self.bitvec_sort(width);
        let id = self.alloc_value(width);
        self.lines.push(Line::Unary { id, op, sort, arg });
        id
    }

    pub fn binary(&mut self, op: BinaryOp, lhs: NodeId, rhs: NodeId) -> NodeId {
        let width = match op {
            BinaryOp::Eq
            | BinaryOp::Slt
            | BinaryOp::Slte
            | BinaryOp::Sgt
            | BinaryOp::Sgte
            | BinaryOp::Ult
            | BinaryOp::Ulte
            | BinaryOp::Ugt
            | BinaryOp::Ugte => 1,
            _ => self.width_of(lhs),
        };
        let sort = self.bitvec_sort(width);
        let id = self.alloc_value(width);
        self.lines.push(Line::Binary {
            id,
            op,
            sort,
            lhs,
            rhs,
        });
        id
    }

    pub fn ite(&mut self, cond: NodeId, then_value: NodeId, else_value: NodeId) -> NodeId {
        let width = self.width_of(then_value);
        let sort = self.bitvec_sort(width);
        let id = self.alloc_value(width);
        self.lines.push(Line::Ite {
            id,
            sort,
            cond,
            then_value,
            else_value,
        });
        id
    }

    pub fn slice(&mut self, value: NodeId, upper: u32, lower: u32) -> NodeId {
        let width = upper - lower + 1;
        let sort = self.bitvec_sort(width);
        let id = self.alloc_value(width);
        self.lines.push(Line::Slice {
            id,
            sort,
            value,
            upper,
            lower,
        });
        id
    }

    pub fn uext(&mut self, value: NodeId, amount: u32) -> NodeId {
        let width = self.width_of(value) + amount;
        let sort = self.bitvec_sort(width);
        let id = self.alloc_value(width);
        self.lines.push(Line::Uext {
            id,
            sort,
            value,
            amount,
        });
        id
    }

    pub fn sext(&mut self, value: NodeId, amount: u32) -> NodeId {
        let width = self.width_of(value) + amount;
        let sort = self.bitvec_sort(width);
        let id = self.alloc_value(width);
        self.lines.push(Line::Sext {
            id,
            sort,
            value,
            amount,
        });
        id
    }

    pub fn init(&mut self, state: NodeId, value: NodeId) -> NodeId {
        let width = self.width_of(state);
        let sort = self.bitvec_sort(width);
        let id = self.alloc_id();
        self.lines.push(Line::Init {
            id,
            sort,
            state,
            value,
        });
        id
    }

    pub fn next(&mut self, state: NodeId, value: NodeId) -> NodeId {
        let width = self.width_of(state);
        let sort = self.bitvec_sort(width);
        let id = self.alloc_id();
        self.lines.push(Line::Next {
            id,
            sort,
            state,
            value,
        });
        id
    }

    pub fn bad(&mut self, cond: NodeId, symbol: Option<String>) -> NodeId {
        let id = self.alloc_id();
        self.lines.push(Line::Bad { id, cond, symbol });
        id
    }

    fn alloc_id(&mut self) -> NodeId {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn alloc_value(&mut self, width: u32) -> NodeId {
        let id = self.alloc_id();
        self.width_by_node.insert(id, width);
        id
    }
}

fn normalize_to_width(value: u128, width: u32) -> u128 {
    if width >= 128 {
        value
    } else {
        let mask = (1u128 << width) - 1;
        value & mask
    }
}

#[cfg(test)]
mod tests {
    use super::{BinaryOp, Builder};

    #[test]
    fn serializes_small_program() {
        let mut builder = Builder::new();
        let x = builder.state(32, "x");
        let zero = builder.zero(32);
        let one = builder.one(32);
        let x_next = builder.binary(BinaryOp::Add, x, one);
        let is_bad = builder.binary(BinaryOp::Eq, x, zero);

        builder.init(x, zero);
        builder.next(x, x_next);
        builder.bad(is_bad, Some("x_is_zero".to_owned()));

        let text = builder.finish().to_text();
        assert!(text.contains("state"));
        assert!(text.contains("next"));
        assert!(text.contains("bad"));
    }
}
