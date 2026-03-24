use serde::{Deserialize, Serialize};
use zkpv_c0_ast::{BinaryOp, UnaryOp};
use zkpv_c0_lowering as lowering;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScalarType {
    pub width: u32,
    pub signed: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExprType {
    Bool,
    Scalar(ScalarType),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypedExpr {
    pub ty: ExprType,
    pub kind: ExprKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExprKind {
    Var(String),
    Const(u64),
    Nondet {
        symbol: String,
    },
    Cast {
        expr: Box<TypedExpr>,
        target: ScalarType,
    },
    Unary {
        op: UnaryOp,
        expr: Box<TypedExpr>,
    },
    Ite {
        cond: Box<TypedExpr>,
        then_expr: Box<TypedExpr>,
        else_expr: Box<TypedExpr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<TypedExpr>,
        rhs: Box<TypedExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum VarKind {
    Global,
    Local,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VariableDecl {
    pub name: String,
    pub source_name: String,
    pub ty: ScalarType,
    pub kind: VarKind,
    pub init: TypedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BasicBlock {
    pub id: u32,
    pub actions: Vec<Action>,
    pub terminator: Terminator,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Action {
    Assign { target: String, value: TypedExpr },
    Assert(TypedExpr),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Terminator {
    Goto(u32),
    Branch {
        cond: TypedExpr,
        then_block: u32,
        else_block: u32,
    },
    Return,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerificationProgram {
    pub variables: Vec<VariableDecl>,
    pub blocks: Vec<BasicBlock>,
    pub entry_block: u32,
    pub exit_block: u32,
    pub error_block: u32,
}

impl From<lowering::ScalarType> for ScalarType {
    fn from(value: lowering::ScalarType) -> Self {
        Self {
            width: value.width,
            signed: value.signed,
        }
    }
}

impl From<lowering::ExprType> for ExprType {
    fn from(value: lowering::ExprType) -> Self {
        match value {
            lowering::ExprType::Bool => Self::Bool,
            lowering::ExprType::Scalar(ty) => Self::Scalar(ty.into()),
        }
    }
}

impl From<lowering::TypedExpr> for TypedExpr {
    fn from(value: lowering::TypedExpr) -> Self {
        Self {
            ty: value.ty.into(),
            kind: value.kind.into(),
        }
    }
}

impl From<lowering::ExprKind> for ExprKind {
    fn from(value: lowering::ExprKind) -> Self {
        match value {
            lowering::ExprKind::Var(name) => Self::Var(name),
            lowering::ExprKind::Const(value) => Self::Const(value),
            lowering::ExprKind::Nondet { symbol } => Self::Nondet { symbol },
            lowering::ExprKind::Cast { expr, target } => Self::Cast {
                expr: Box::new((*expr).into()),
                target: target.into(),
            },
            lowering::ExprKind::Unary { op, expr } => Self::Unary {
                op,
                expr: Box::new((*expr).into()),
            },
            lowering::ExprKind::Ite {
                cond,
                then_expr,
                else_expr,
            } => Self::Ite {
                cond: Box::new((*cond).into()),
                then_expr: Box::new((*then_expr).into()),
                else_expr: Box::new((*else_expr).into()),
            },
            lowering::ExprKind::Binary { op, lhs, rhs } => Self::Binary {
                op,
                lhs: Box::new((*lhs).into()),
                rhs: Box::new((*rhs).into()),
            },
        }
    }
}

impl From<lowering::VarKind> for VarKind {
    fn from(value: lowering::VarKind) -> Self {
        match value {
            lowering::VarKind::Global => Self::Global,
            lowering::VarKind::Local => Self::Local,
        }
    }
}

impl From<lowering::VariableDecl> for VariableDecl {
    fn from(value: lowering::VariableDecl) -> Self {
        Self {
            name: value.name,
            source_name: value.source_name,
            ty: value.ty.into(),
            kind: value.kind.into(),
            init: value.init.into(),
        }
    }
}

impl From<lowering::Action> for Action {
    fn from(value: lowering::Action) -> Self {
        match value {
            lowering::Action::Assign { target, value } => Self::Assign {
                target,
                value: value.into(),
            },
            lowering::Action::Assert(expr) => Self::Assert(expr.into()),
        }
    }
}

impl From<lowering::Terminator> for Terminator {
    fn from(value: lowering::Terminator) -> Self {
        match value {
            lowering::Terminator::Goto(target) => Self::Goto(target as u32),
            lowering::Terminator::Branch {
                cond,
                then_block,
                else_block,
            } => Self::Branch {
                cond: cond.into(),
                then_block: then_block as u32,
                else_block: else_block as u32,
            },
            lowering::Terminator::Return => Self::Return,
        }
    }
}

impl TryFrom<lowering::NormalizedProgram> for VerificationProgram {
    type Error = String;

    fn try_from(value: lowering::NormalizedProgram) -> Result<Self, Self::Error> {
        let mut blocks = Vec::with_capacity(value.blocks.len());
        for block in value.blocks {
            let terminator = block
                .terminator
                .ok_or_else(|| format!("block {} is missing a terminator", block.id))?;
            blocks.push(BasicBlock {
                id: block.id as u32,
                actions: block.actions.into_iter().map(Into::into).collect(),
                terminator: terminator.into(),
            });
        }

        Ok(Self {
            variables: value.variables.into_iter().map(Into::into).collect(),
            blocks,
            entry_block: value.entry_block as u32,
            exit_block: value.exit_block as u32,
            error_block: value.error_block as u32,
        })
    }
}
