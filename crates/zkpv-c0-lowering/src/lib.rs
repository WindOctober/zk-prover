//! Minimal normalization and BTOR2-like lowering for the supported C0 subset.

use std::collections::BTreeMap;

use thiserror::Error;
use zkpv_btor2::{
    BinaryOp as BtorBinaryOp, Builder as BtorBuilder, NodeId, Program as BtorProgram,
    UnaryOp as BtorUnaryOp,
};
use zkpv_c0_ast::{
    AssignOp, BinaryOp, Block, Expr, ForInit, Function, Item, PostfixOp, Stmt, TranslationUnit,
    Type, UnaryOp, VarDeclStmt,
};
use zkpv_c0_parser::{parse_translation_unit, ParseError};

pub const CRATE_NAME: &str = "zkpv-c0-lowering";

pub type BlockId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScalarType {
    pub width: u32,
    pub signed: bool,
}

impl ScalarType {
    pub const fn int() -> Self {
        Self {
            width: 32,
            signed: true,
        }
    }

    pub const fn uint() -> Self {
        Self {
            width: 32,
            signed: false,
        }
    }

    pub const fn char() -> Self {
        Self {
            width: 8,
            signed: true,
        }
    }

    pub const fn uchar() -> Self {
        Self {
            width: 8,
            signed: false,
        }
    }

    pub const fn short() -> Self {
        Self {
            width: 16,
            signed: true,
        }
    }

    pub const fn ushort() -> Self {
        Self {
            width: 16,
            signed: false,
        }
    }

    pub const fn long() -> Self {
        Self {
            width: 32,
            signed: true,
        }
    }

    pub const fn ulong() -> Self {
        Self {
            width: 32,
            signed: false,
        }
    }

    fn from_ast(ty: &Type) -> Result<Self, LoweringError> {
        match ty {
            Type::Int => Ok(Self::int()),
            Type::UnsignedInt => Ok(Self::uint()),
            Type::Short => Ok(Self::short()),
            Type::UnsignedShort => Ok(Self::ushort()),
            Type::Long => Ok(Self::long()),
            Type::UnsignedLong => Ok(Self::ulong()),
            Type::Char | Type::SignedChar => Ok(Self::char()),
            Type::UnsignedChar => Ok(Self::uchar()),
            Type::Void => Err(LoweringError::UnsupportedType(
                "void variables are not supported".to_owned(),
            )),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprType {
    Bool,
    Scalar(ScalarType),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedExpr {
    pub ty: ExprType,
    pub kind: ExprKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarKind {
    Global,
    Local,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariableDecl {
    pub name: String,
    pub source_name: String,
    pub ty: ScalarType,
    pub kind: VarKind,
    pub init: TypedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BasicBlock {
    pub id: BlockId,
    pub actions: Vec<Action>,
    pub terminator: Option<Terminator>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Action {
    Assign { target: String, value: TypedExpr },
    Assert(TypedExpr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminator {
    Goto(BlockId),
    Branch {
        cond: TypedExpr,
        then_block: BlockId,
        else_block: BlockId,
    },
    Return,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalizedProgram {
    pub variables: Vec<VariableDecl>,
    pub blocks: Vec<BasicBlock>,
    pub entry_block: BlockId,
    pub exit_block: BlockId,
    pub error_block: BlockId,
}

#[derive(Debug, Error)]
pub enum LoweringError {
    #[error("parse error: {0}")]
    Parse(#[from] ParseError),
    #[error("translation unit does not contain a parseable `main` function")]
    MissingMain,
    #[error("unsupported type: {0}")]
    UnsupportedType(String),
    #[error("unsupported expression: {0}")]
    UnsupportedExpr(String),
    #[error("unsupported statement: {0}")]
    UnsupportedStmt(String),
    #[error("unsupported function call: {0}")]
    UnsupportedCall(String),
    #[error("unsupported lvalue in assignment")]
    UnsupportedLvalue,
    #[error("unknown variable `{0}`")]
    UnknownVariable(String),
    #[error("internal lowering error: {0}")]
    Internal(String),
}

pub fn lower_source_to_btor2(source: &str) -> Result<BtorProgram, LoweringError> {
    let unit = parse_translation_unit(source)?;
    let normalized = lower_translation_unit(&unit)?;
    Ok(encode_btor2(&normalized))
}

pub fn lower_translation_unit(unit: &TranslationUnit) -> Result<NormalizedProgram, LoweringError> {
    let mut ctx = LoweringContext::new();
    ctx.lower_globals(unit)?;

    let main = unit.main_function().ok_or(LoweringError::MissingMain)?;
    ctx.lower_main(main)?;
    ctx.finish()
}

struct LoweringContext {
    program: NormalizedProgram,
    prologue_actions: Vec<Action>,
    scopes: Vec<BTreeMap<String, String>>,
    variable_types: BTreeMap<String, ScalarType>,
    name_counters: BTreeMap<String, u32>,
    next_nondet: u32,
}

impl LoweringContext {
    fn new() -> Self {
        let mut program = NormalizedProgram {
            variables: Vec::new(),
            blocks: Vec::new(),
            entry_block: 0,
            exit_block: 0,
            error_block: 0,
        };

        let entry_block = push_block(&mut program.blocks);
        let exit_block = push_block(&mut program.blocks);
        let error_block = push_block(&mut program.blocks);

        program.entry_block = entry_block;
        program.exit_block = exit_block;
        program.error_block = error_block;

        Self {
            program,
            prologue_actions: Vec::new(),
            scopes: vec![BTreeMap::new()],
            variable_types: BTreeMap::new(),
            name_counters: BTreeMap::new(),
            next_nondet: 0,
        }
    }

    fn finish(mut self) -> Result<NormalizedProgram, LoweringError> {
        for block in &mut self.program.blocks {
            if block.terminator.is_none() {
                block.terminator = Some(Terminator::Goto(self.program.error_block));
            }
        }

        self.program.blocks[self.program.exit_block].terminator =
            Some(Terminator::Goto(self.program.exit_block));
        self.program.blocks[self.program.error_block].terminator =
            Some(Terminator::Goto(self.program.error_block));

        Ok(self.program)
    }

    fn lower_globals(&mut self, unit: &TranslationUnit) -> Result<(), LoweringError> {
        for item in &unit.items {
            if let Item::GlobalVar(stmt) = item {
                self.declare_globals(stmt)?;
            }
        }
        Ok(())
    }

    fn lower_main(&mut self, main: &Function) -> Result<(), LoweringError> {
        if !main.params.is_empty() {
            return Err(LoweringError::UnsupportedStmt(
                "main parameters are not supported yet".to_owned(),
            ));
        }

        self.push_scope();
        self.program.blocks[self.program.entry_block]
            .actions
            .extend(self.prologue_actions.clone());
        let end_block = self.lower_block(self.program.entry_block, &main.body)?;
        if let Some(block) = end_block {
            self.set_terminator(block, Terminator::Return)?;
        }
        self.pop_scope();
        Ok(())
    }

    fn declare_globals(&mut self, stmt: &VarDeclStmt) -> Result<(), LoweringError> {
        let ty = ScalarType::from_ast(&stmt.ty)?;
        for declarator in &stmt.declarators {
            let lowered_name = self.bind_name(&declarator.name, ty, VarKind::Global, zero_expr(ty));
            self.current_scope_mut()
                .insert(declarator.name.clone(), lowered_name);

            if let Some(init) = &declarator.init {
                let target = self.resolve_name(&declarator.name)?;
                let value = cast_scalar_expr(self.lower_value_expr(init)?, ty);
                self.prologue_actions.push(Action::Assign { target, value });
            }
        }
        Ok(())
    }

    fn lower_block(
        &mut self,
        start_block: BlockId,
        block: &Block,
    ) -> Result<Option<BlockId>, LoweringError> {
        self.push_scope();
        let mut current = Some(start_block);
        for stmt in &block.stmts {
            let Some(block_id) = current else { break };
            current = self.lower_stmt(block_id, stmt)?;
        }
        self.pop_scope();
        Ok(current)
    }

    fn lower_stmt(
        &mut self,
        current: BlockId,
        stmt: &Stmt,
    ) -> Result<Option<BlockId>, LoweringError> {
        match stmt {
            Stmt::Block(block) => self.lower_block(current, block),
            Stmt::VarDecl(stmt) => {
                self.lower_var_decl_stmt(current, stmt)?;
                Ok(Some(current))
            }
            Stmt::If {
                cond,
                then_branch,
                else_branch,
            } => self.lower_if(current, cond, then_branch, else_branch.as_deref()),
            Stmt::While { cond, body } => self.lower_while(current, cond, body),
            Stmt::For {
                init,
                cond,
                step,
                body,
            } => self.lower_for(current, init.as_ref(), cond.as_ref(), step.as_ref(), body),
            Stmt::Return(expr) => {
                if let Some(expr) = expr {
                    let _ = self.lower_value_expr(expr)?;
                }
                self.set_terminator(current, Terminator::Return)?;
                Ok(None)
            }
            Stmt::Expr(expr) => self.lower_expr_stmt(current, expr),
            Stmt::Empty => Ok(Some(current)),
        }
    }

    fn lower_var_decl_stmt(
        &mut self,
        current: BlockId,
        stmt: &VarDeclStmt,
    ) -> Result<(), LoweringError> {
        let ty = ScalarType::from_ast(&stmt.ty)?;
        for declarator in &stmt.declarators {
            let lowered_name = self.bind_name(&declarator.name, ty, VarKind::Local, zero_expr(ty));
            self.current_scope_mut()
                .insert(declarator.name.clone(), lowered_name.clone());

            if let Some(init) = &declarator.init {
                let value = cast_scalar_expr(self.lower_value_expr(init)?, ty);
                self.program.blocks[current].actions.push(Action::Assign {
                    target: lowered_name,
                    value,
                });
            }
        }
        Ok(())
    }

    fn lower_if(
        &mut self,
        current: BlockId,
        cond: &Expr,
        then_branch: &Stmt,
        else_branch: Option<&Stmt>,
    ) -> Result<Option<BlockId>, LoweringError> {
        let cond = self.lower_condition_expr(cond)?;
        let then_block = self.new_block();
        let join_block = self.new_block();
        let else_block = else_branch.map(|_| self.new_block()).unwrap_or(join_block);

        self.set_terminator(
            current,
            Terminator::Branch {
                cond,
                then_block,
                else_block,
            },
        )?;

        let then_end = self.lower_stmt(then_block, then_branch)?;
        let else_end = if let Some(else_branch) = else_branch {
            self.lower_stmt(else_block, else_branch)?
        } else {
            Some(join_block)
        };

        let mut join_reachable = false;
        if let Some(block) = then_end {
            self.set_terminator(block, Terminator::Goto(join_block))?;
            join_reachable = true;
        }
        if let Some(block) = else_end {
            if block != join_block {
                self.set_terminator(block, Terminator::Goto(join_block))?;
            }
            join_reachable = true;
        }

        Ok(join_reachable.then_some(join_block))
    }

    fn lower_while(
        &mut self,
        current: BlockId,
        cond: &Expr,
        body: &Stmt,
    ) -> Result<Option<BlockId>, LoweringError> {
        let cond_block = self.new_block();
        let body_block = self.new_block();
        let exit_block = self.new_block();
        let lowered_cond = self.lower_condition_expr(cond)?;

        self.set_terminator(current, Terminator::Goto(cond_block))?;
        self.set_terminator(
            cond_block,
            Terminator::Branch {
                cond: lowered_cond,
                then_block: body_block,
                else_block: exit_block,
            },
        )?;

        let body_end = self.lower_stmt(body_block, body)?;
        if let Some(end) = body_end {
            self.set_terminator(end, Terminator::Goto(cond_block))?;
        }

        Ok(Some(exit_block))
    }

    fn lower_for(
        &mut self,
        current: BlockId,
        init: Option<&ForInit>,
        cond: Option<&Expr>,
        step: Option<&Expr>,
        body: &Stmt,
    ) -> Result<Option<BlockId>, LoweringError> {
        self.push_scope();

        let mut current = current;
        if let Some(init) = init {
            match init {
                ForInit::VarDecl(stmt) => self.lower_var_decl_stmt(current, stmt)?,
                ForInit::Expr(expr) => {
                    let next = self.lower_expr_stmt(current, expr)?;
                    let Some(block) = next else {
                        self.pop_scope();
                        return Ok(None);
                    };
                    current = block;
                }
            }
        }

        let cond_block = self.new_block();
        let body_block = self.new_block();
        let exit_block = self.new_block();

        self.set_terminator(current, Terminator::Goto(cond_block))?;

        let cond_expr = if let Some(cond) = cond {
            self.lower_condition_expr(cond)?
        } else {
            true_expr()
        };
        self.set_terminator(
            cond_block,
            Terminator::Branch {
                cond: cond_expr,
                then_block: body_block,
                else_block: exit_block,
            },
        )?;

        let body_end = self.lower_stmt(body_block, body)?;
        if let Some(end) = body_end {
            let end = if let Some(step) = step {
                match self.lower_expr_stmt(end, step)? {
                    Some(block) => block,
                    None => {
                        self.pop_scope();
                        return Ok(Some(exit_block));
                    }
                }
            } else {
                end
            };
            self.set_terminator(end, Terminator::Goto(cond_block))?;
        }

        self.pop_scope();
        Ok(Some(exit_block))
    }

    fn lower_expr_stmt(
        &mut self,
        current: BlockId,
        expr: &Expr,
    ) -> Result<Option<BlockId>, LoweringError> {
        match expr {
            Expr::Assign { op, lhs, rhs } => {
                let target = self.lower_assignment_target(lhs)?;
                let ty = self.lookup_var_type(&target)?;
                let rhs = self.lower_value_expr(rhs)?;
                let value = match op {
                    AssignOp::Assign => cast_scalar_expr(rhs, ty),
                    AssignOp::AddAssign | AssignOp::SubAssign => {
                        let lhs_expr = TypedExpr::var(target.clone(), ty);
                        let rhs = cast_scalar_expr(rhs, ty);
                        let op = match op {
                            AssignOp::AddAssign => BinaryOp::Add,
                            AssignOp::SubAssign => BinaryOp::Sub,
                            AssignOp::Assign => unreachable!(),
                        };
                        TypedExpr {
                            ty: ExprType::Scalar(ty),
                            kind: ExprKind::Binary {
                                op,
                                lhs: Box::new(lhs_expr),
                                rhs: Box::new(rhs),
                            },
                        }
                    }
                };
                self.program.blocks[current]
                    .actions
                    .push(Action::Assign { target, value });
                Ok(Some(current))
            }
            Expr::Unary { op, expr } => {
                let delta = match op {
                    UnaryOp::PreInc => 1i64,
                    UnaryOp::PreDec => -1i64,
                    _ => {
                        let _ = self.lower_value_expr(&Expr::Unary {
                            op: *op,
                            expr: expr.clone(),
                        })?;
                        return Ok(Some(current));
                    }
                };
                self.lower_inc_dec_stmt(current, expr, delta)?;
                Ok(Some(current))
            }
            Expr::Postfix { op, expr } => {
                let delta = match op {
                    PostfixOp::PostInc => 1i64,
                    PostfixOp::PostDec => -1i64,
                };
                self.lower_inc_dec_stmt(current, expr, delta)?;
                Ok(Some(current))
            }
            Expr::Call { callee, args } if callee == "__VERIFIER_assert" => {
                if args.len() != 1 {
                    return Err(LoweringError::UnsupportedCall(format!(
                        "{callee} expects exactly one argument"
                    )));
                }
                let cond = self.lower_condition_expr(&args[0])?;
                self.program.blocks[current]
                    .actions
                    .push(Action::Assert(cond));
                Ok(Some(current))
            }
            Expr::Call { callee, args } if callee == "reach_error" || callee == "abort" => {
                if !args.is_empty() {
                    return Err(LoweringError::UnsupportedCall(format!(
                        "{callee} does not support arguments in this lowering"
                    )));
                }
                self.set_terminator(current, Terminator::Goto(self.program.error_block))?;
                Ok(None)
            }
            _ => {
                let _ = self.lower_value_expr(expr)?;
                Ok(Some(current))
            }
        }
    }

    fn lower_inc_dec_stmt(
        &mut self,
        current: BlockId,
        expr: &Expr,
        delta: i64,
    ) -> Result<(), LoweringError> {
        let target = self.lower_assignment_target(expr)?;
        let ty = self.lookup_var_type(&target)?;
        let delta_expr = literal_expr(delta.unsigned_abs(), ScalarType::int());
        let lhs = TypedExpr::var(target.clone(), ty);
        let rhs = cast_scalar_expr(delta_expr, ty);
        let value = TypedExpr {
            ty: ExprType::Scalar(ty),
            kind: ExprKind::Binary {
                op: if delta >= 0 {
                    BinaryOp::Add
                } else {
                    BinaryOp::Sub
                },
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
        };
        self.program.blocks[current]
            .actions
            .push(Action::Assign { target, value });
        Ok(())
    }

    fn lower_value_expr(&mut self, expr: &Expr) -> Result<TypedExpr, LoweringError> {
        match expr {
            Expr::Ident(name) => {
                let lowered_name = self.resolve_name(name)?;
                let ty = self.lookup_var_type(&lowered_name)?;
                Ok(TypedExpr::var(lowered_name, ty))
            }
            Expr::IntLiteral(raw) => {
                let (value, ty) = parse_int_literal(raw)?;
                Ok(literal_expr(value, ty))
            }
            Expr::Call { callee, args } => self.lower_value_call(callee, args),
            Expr::Conditional {
                cond,
                then_expr,
                else_expr,
            } => self.lower_conditional_expr(cond, then_expr, else_expr),
            Expr::Cast { ty, expr } => {
                let expr = self.lower_value_expr(expr)?;
                let target = ScalarType::from_ast(ty)?;
                Ok(cast_scalar_expr(expr, target))
            }
            Expr::Unary { op, expr } => self.lower_unary_expr(*op, expr),
            Expr::Binary { op, lhs, rhs } => self.lower_binary_expr(*op, lhs, rhs),
            Expr::Assign { .. } => Err(LoweringError::UnsupportedExpr(
                "assignment expressions are only supported as standalone statements".to_owned(),
            )),
            Expr::Postfix { .. } => Err(LoweringError::UnsupportedExpr(
                "postfix update expressions are only supported as standalone statements".to_owned(),
            )),
        }
    }

    fn lower_conditional_expr(
        &mut self,
        cond: &Expr,
        then_expr: &Expr,
        else_expr: &Expr,
    ) -> Result<TypedExpr, LoweringError> {
        let cond = as_bool_expr(self.lower_value_expr(cond)?);
        let then_expr = self.lower_value_expr(then_expr)?;
        let else_expr = self.lower_value_expr(else_expr)?;

        let ty = match (then_expr.ty, else_expr.ty) {
            (ExprType::Bool, ExprType::Bool) => ExprType::Bool,
            (ExprType::Scalar(lhs), ExprType::Scalar(rhs)) => ExprType::Scalar(common_scalar_type(
                ExprType::Scalar(lhs),
                ExprType::Scalar(rhs),
            )?),
            _ => {
                return Err(LoweringError::UnsupportedExpr(
                    "conditional expressions require matching scalar or boolean branch types"
                        .to_owned(),
                ))
            }
        };

        let (then_expr, else_expr) = match ty {
            ExprType::Bool => (then_expr, else_expr),
            ExprType::Scalar(target) => (
                cast_scalar_expr(then_expr, target),
                cast_scalar_expr(else_expr, target),
            ),
        };

        Ok(TypedExpr {
            ty,
            kind: ExprKind::Ite {
                cond: Box::new(cond),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
            },
        })
    }

    fn lower_value_call(
        &mut self,
        callee: &str,
        args: &[Expr],
    ) -> Result<TypedExpr, LoweringError> {
        if !args.is_empty() {
            return Err(LoweringError::UnsupportedCall(format!(
                "{callee} value calls with arguments are not supported"
            )));
        }

        let ty = match callee {
            "__VERIFIER_nondet_int" => ScalarType::int(),
            "__VERIFIER_nondet_uint" => ScalarType::uint(),
            _ => return Err(LoweringError::UnsupportedCall(callee.to_owned())),
        };

        let symbol = format!("{callee}${}", self.next_nondet);
        self.next_nondet += 1;

        Ok(TypedExpr {
            ty: ExprType::Scalar(ty),
            kind: ExprKind::Nondet { symbol },
        })
    }

    fn lower_unary_expr(&mut self, op: UnaryOp, expr: &Expr) -> Result<TypedExpr, LoweringError> {
        let expr = self.lower_value_expr(expr)?;
        match op {
            UnaryOp::Plus => {
                ensure_scalar(expr.ty)?;
                Ok(expr)
            }
            UnaryOp::Minus | UnaryOp::BitNot => {
                let ty = ensure_scalar(expr.ty)?;
                Ok(TypedExpr {
                    ty: ExprType::Scalar(ty),
                    kind: ExprKind::Unary {
                        op,
                        expr: Box::new(expr),
                    },
                })
            }
            UnaryOp::Not => Ok(TypedExpr {
                ty: ExprType::Bool,
                kind: ExprKind::Unary {
                    op,
                    expr: Box::new(as_bool_expr(expr)),
                },
            }),
            UnaryOp::PreInc | UnaryOp::PreDec => Err(LoweringError::UnsupportedExpr(
                "prefix update expressions are only supported as standalone statements".to_owned(),
            )),
        }
    }

    fn lower_binary_expr(
        &mut self,
        op: BinaryOp,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Result<TypedExpr, LoweringError> {
        match op {
            BinaryOp::LogicalAnd | BinaryOp::LogicalOr => {
                let lhs = as_bool_expr(self.lower_value_expr(lhs)?);
                let rhs = as_bool_expr(self.lower_value_expr(rhs)?);
                Ok(TypedExpr {
                    ty: ExprType::Bool,
                    kind: ExprKind::Binary {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                })
            }
            BinaryOp::Eq | BinaryOp::Ne => {
                let lhs = self.lower_value_expr(lhs)?;
                let rhs = self.lower_value_expr(rhs)?;
                let common = common_scalar_type(lhs.ty, rhs.ty)?;
                Ok(TypedExpr {
                    ty: ExprType::Bool,
                    kind: ExprKind::Binary {
                        op,
                        lhs: Box::new(cast_scalar_expr(lhs, common)),
                        rhs: Box::new(cast_scalar_expr(rhs, common)),
                    },
                })
            }
            BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                let lhs = self.lower_value_expr(lhs)?;
                let rhs = self.lower_value_expr(rhs)?;
                let common = common_scalar_type(lhs.ty, rhs.ty)?;
                Ok(TypedExpr {
                    ty: ExprType::Bool,
                    kind: ExprKind::Binary {
                        op,
                        lhs: Box::new(cast_scalar_expr(lhs, common)),
                        rhs: Box::new(cast_scalar_expr(rhs, common)),
                    },
                })
            }
            _ => {
                let lhs = self.lower_value_expr(lhs)?;
                let rhs = self.lower_value_expr(rhs)?;
                let common = common_scalar_type(lhs.ty, rhs.ty)?;
                Ok(TypedExpr {
                    ty: ExprType::Scalar(common),
                    kind: ExprKind::Binary {
                        op,
                        lhs: Box::new(cast_scalar_expr(lhs, common)),
                        rhs: Box::new(cast_scalar_expr(rhs, common)),
                    },
                })
            }
        }
    }

    fn lower_condition_expr(&mut self, expr: &Expr) -> Result<TypedExpr, LoweringError> {
        Ok(as_bool_expr(self.lower_value_expr(expr)?))
    }

    fn lower_assignment_target(&self, expr: &Expr) -> Result<String, LoweringError> {
        match expr {
            Expr::Ident(name) => self.resolve_name(name),
            _ => Err(LoweringError::UnsupportedLvalue),
        }
    }

    fn new_block(&mut self) -> BlockId {
        push_block(&mut self.program.blocks)
    }

    fn set_terminator(
        &mut self,
        block: BlockId,
        terminator: Terminator,
    ) -> Result<(), LoweringError> {
        let slot = &mut self.program.blocks[block].terminator;
        if slot.is_some() {
            return Err(LoweringError::Internal(format!(
                "block {block} already has a terminator"
            )));
        }
        *slot = Some(terminator);
        Ok(())
    }

    fn bind_name(
        &mut self,
        source_name: &str,
        ty: ScalarType,
        kind: VarKind,
        init: TypedExpr,
    ) -> String {
        let entry = self
            .name_counters
            .entry(source_name.to_owned())
            .or_insert(0);
        let lowered_name = if *entry == 0 {
            source_name.to_owned()
        } else {
            format!("{source_name}#{}", *entry)
        };
        *entry += 1;

        self.variable_types.insert(lowered_name.clone(), ty);
        self.program.variables.push(VariableDecl {
            name: lowered_name.clone(),
            source_name: source_name.to_owned(),
            ty,
            kind,
            init,
        });
        lowered_name
    }

    fn resolve_name(&self, name: &str) -> Result<String, LoweringError> {
        for scope in self.scopes.iter().rev() {
            if let Some(lowered) = scope.get(name) {
                return Ok(lowered.clone());
            }
        }
        Err(LoweringError::UnknownVariable(name.to_owned()))
    }

    fn lookup_var_type(&self, lowered_name: &str) -> Result<ScalarType, LoweringError> {
        self.variable_types
            .get(lowered_name)
            .copied()
            .ok_or_else(|| LoweringError::UnknownVariable(lowered_name.to_owned()))
    }

    fn push_scope(&mut self) {
        self.scopes.push(BTreeMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn current_scope_mut(&mut self) -> &mut BTreeMap<String, String> {
        self.scopes
            .last_mut()
            .expect("scope stack should not be empty")
    }
}

fn push_block(blocks: &mut Vec<BasicBlock>) -> BlockId {
    let id = blocks.len();
    blocks.push(BasicBlock {
        id,
        actions: Vec::new(),
        terminator: None,
    });
    id
}

fn ensure_scalar(ty: ExprType) -> Result<ScalarType, LoweringError> {
    match ty {
        ExprType::Scalar(ty) => Ok(ty),
        ExprType::Bool => Err(LoweringError::UnsupportedExpr(
            "boolean expression used where a scalar value was expected".to_owned(),
        )),
    }
}

fn common_scalar_type(lhs: ExprType, rhs: ExprType) -> Result<ScalarType, LoweringError> {
    let lhs = ensure_scalar(lhs)?;
    let rhs = ensure_scalar(rhs)?;
    Ok(if lhs.width > rhs.width {
        lhs
    } else if rhs.width > lhs.width {
        rhs
    } else if !lhs.signed || !rhs.signed {
        ScalarType {
            width: lhs.width,
            signed: false,
        }
    } else {
        lhs
    })
}

fn literal_expr(value: u64, ty: ScalarType) -> TypedExpr {
    TypedExpr {
        ty: ExprType::Scalar(ty),
        kind: ExprKind::Const(value),
    }
}

fn zero_expr(ty: ScalarType) -> TypedExpr {
    literal_expr(0, ty)
}

fn true_expr() -> TypedExpr {
    TypedExpr {
        ty: ExprType::Bool,
        kind: ExprKind::Const(1),
    }
}

fn cast_scalar_expr(expr: TypedExpr, target: ScalarType) -> TypedExpr {
    match expr.ty {
        ExprType::Scalar(current) if current == target => expr,
        _ => TypedExpr {
            ty: ExprType::Scalar(target),
            kind: ExprKind::Cast {
                expr: Box::new(expr),
                target,
            },
        },
    }
}

fn as_bool_expr(expr: TypedExpr) -> TypedExpr {
    if expr.ty == ExprType::Bool {
        return expr;
    }
    let scalar = match expr.ty {
        ExprType::Bool => unreachable!(),
        ExprType::Scalar(ty) => ty,
    };
    TypedExpr {
        ty: ExprType::Bool,
        kind: ExprKind::Binary {
            op: BinaryOp::Ne,
            lhs: Box::new(expr),
            rhs: Box::new(zero_expr(scalar)),
        },
    }
}

impl TypedExpr {
    fn var(name: String, ty: ScalarType) -> Self {
        Self {
            ty: ExprType::Scalar(ty),
            kind: ExprKind::Var(name),
        }
    }
}

fn parse_int_literal(raw: &str) -> Result<(u64, ScalarType), LoweringError> {
    let is_unsigned = raw.chars().any(|ch| ch == 'u' || ch == 'U');
    let digits = raw
        .trim_end_matches(|ch: char| matches!(ch, 'u' | 'U' | 'l' | 'L'))
        .replace('_', "");
    let value = if let Some(hex) = digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        u64::from_str_radix(hex, 16)
    } else {
        digits.parse::<u64>()
    }
    .map_err(|err| {
        LoweringError::UnsupportedExpr(format!("failed to parse integer literal `{raw}`: {err}"))
    })?;
    let ty = if is_unsigned || value > i32::MAX as u64 {
        ScalarType::uint()
    } else {
        ScalarType::int()
    };
    Ok((value, ty))
}

pub fn encode_btor2(program: &NormalizedProgram) -> BtorProgram {
    let mut builder = BtorBuilder::new();
    let pc_width = bit_width_for(program.blocks.len().max(2) as u64 - 1);
    let entry_pc = builder.const_u64(pc_width, program.entry_block as u64);
    let error_pc = builder.const_u64(pc_width, program.error_block as u64);
    let pc_state = builder.state(pc_width, "pc");

    let mut zero_inits = BTreeMap::new();
    zero_inits.insert(pc_width, builder.zero(pc_width));
    for variable in &program.variables {
        zero_inits
            .entry(variable.ty.width)
            .or_insert_with(|| builder.zero(variable.ty.width));
    }

    let mut state_nodes = BTreeMap::new();
    for variable in &program.variables {
        let state = builder.state(variable.ty.width, variable.name.clone());
        state_nodes.insert(variable.name.clone(), state);
    }

    let mut input_nodes = BTreeMap::new();
    for variable in &program.variables {
        let init = zero_inits[&variable.ty.width];
        builder.init(state_nodes[&variable.name], init);
    }
    builder.init(pc_state, entry_pc);

    let mut pc_next = entry_pc;
    let mut value_nexts = state_nodes.clone();

    for block in program.blocks.iter().rev() {
        let block_id_const = builder.const_u64(pc_width, block.id as u64);
        let is_active = builder.binary(BtorBinaryOp::Eq, pc_state, block_id_const);
        let mut env = state_nodes.clone();
        let mut path_ok = builder.one(1);

        for action in &block.actions {
            match action {
                Action::Assign { target, value } => {
                    let current = env[target];
                    let next = encode_expr(value, &env, &mut builder, &mut input_nodes);
                    let guarded = builder.ite(path_ok, next, current);
                    env.insert(target.clone(), guarded);
                }
                Action::Assert(cond) => {
                    let cond = encode_bool(cond, &env, &mut builder, &mut input_nodes);
                    path_ok = builder.binary(BtorBinaryOp::And, path_ok, cond);
                }
            }
        }

        let nominal_pc = match block
            .terminator
            .as_ref()
            .expect("all blocks should have a terminator before encoding")
        {
            Terminator::Goto(target) => builder.const_u64(pc_width, *target as u64),
            Terminator::Return => builder.const_u64(pc_width, program.exit_block as u64),
            Terminator::Branch {
                cond,
                then_block,
                else_block,
            } => {
                let cond = encode_bool(cond, &env, &mut builder, &mut input_nodes);
                let then_pc = builder.const_u64(pc_width, *then_block as u64);
                let else_pc = builder.const_u64(pc_width, *else_block as u64);
                builder.ite(cond, then_pc, else_pc)
            }
        };
        let block_pc_next = builder.ite(path_ok, nominal_pc, error_pc);
        pc_next = builder.ite(is_active, block_pc_next, pc_next);

        for variable in &program.variables {
            let candidate = *env
                .get(&variable.name)
                .unwrap_or(&state_nodes[&variable.name]);
            let current = value_nexts[&variable.name];
            let next = builder.ite(is_active, candidate, current);
            value_nexts.insert(variable.name.clone(), next);
        }
    }

    for variable in &program.variables {
        builder.next(state_nodes[&variable.name], value_nexts[&variable.name]);
    }
    builder.next(pc_state, pc_next);

    let error_pc_const = builder.const_u64(pc_width, program.error_block as u64);
    let bad = builder.binary(BtorBinaryOp::Eq, pc_state, error_pc_const);
    builder.bad(bad, Some("reach_error".to_owned()));
    builder.finish()
}

fn encode_bool(
    expr: &TypedExpr,
    env: &BTreeMap<String, NodeId>,
    builder: &mut BtorBuilder,
    inputs: &mut BTreeMap<String, NodeId>,
) -> NodeId {
    let node = encode_expr(expr, env, builder, inputs);
    if matches!(expr.ty, ExprType::Bool) {
        node
    } else {
        let width = match expr.ty {
            ExprType::Bool => 1,
            ExprType::Scalar(ty) => ty.width,
        };
        let zero = builder.zero(width);
        let eq = builder.binary(BtorBinaryOp::Eq, node, zero);
        builder.unary(BtorUnaryOp::Not, eq)
    }
}

fn encode_expr(
    expr: &TypedExpr,
    env: &BTreeMap<String, NodeId>,
    builder: &mut BtorBuilder,
    inputs: &mut BTreeMap<String, NodeId>,
) -> NodeId {
    match &expr.kind {
        ExprKind::Var(name) => env[name],
        ExprKind::Const(value) => match expr.ty {
            ExprType::Bool => builder.const_u64(1, *value),
            ExprType::Scalar(ty) => builder.const_u64(ty.width, *value),
        },
        ExprKind::Nondet { symbol } => {
            if let Some(node) = inputs.get(symbol) {
                *node
            } else {
                let width = match expr.ty {
                    ExprType::Scalar(ty) => ty.width,
                    ExprType::Bool => 1,
                };
                let node = builder.input(width, symbol.clone());
                inputs.insert(symbol.clone(), node);
                node
            }
        }
        ExprKind::Cast { expr, target } => {
            let value = encode_expr(expr, env, builder, inputs);
            cast_node(value, expr.ty, *target, builder)
        }
        ExprKind::Unary { op, expr: inner } => {
            let value = encode_expr(inner, env, builder, inputs);
            match op {
                UnaryOp::Plus => value,
                UnaryOp::Minus => builder.unary(BtorUnaryOp::Neg, value),
                UnaryOp::BitNot | UnaryOp::Not => builder.unary(BtorUnaryOp::Not, value),
                UnaryOp::PreInc | UnaryOp::PreDec => {
                    unreachable!("not lowered into value expressions")
                }
            }
        }
        ExprKind::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            let cond = encode_expr(cond, env, builder, inputs);
            let then_node = encode_expr(then_expr, env, builder, inputs);
            let else_node = encode_expr(else_expr, env, builder, inputs);
            builder.ite(cond, then_node, else_node)
        }
        ExprKind::Binary { op, lhs, rhs } => {
            let lhs_node = encode_expr(lhs, env, builder, inputs);
            let rhs_node = encode_expr(rhs, env, builder, inputs);
            match op {
                BinaryOp::Add => builder.binary(BtorBinaryOp::Add, lhs_node, rhs_node),
                BinaryOp::Sub => builder.binary(BtorBinaryOp::Sub, lhs_node, rhs_node),
                BinaryOp::Mul => builder.binary(BtorBinaryOp::Mul, lhs_node, rhs_node),
                BinaryOp::Div => {
                    let scalar = ensure_scalar(lhs.ty).expect("arithmetic lhs must be scalar");
                    builder.binary(
                        if scalar.signed {
                            BtorBinaryOp::SDiv
                        } else {
                            BtorBinaryOp::UDiv
                        },
                        lhs_node,
                        rhs_node,
                    )
                }
                BinaryOp::Mod => {
                    let scalar = ensure_scalar(lhs.ty).expect("arithmetic lhs must be scalar");
                    builder.binary(
                        if scalar.signed {
                            BtorBinaryOp::SRem
                        } else {
                            BtorBinaryOp::URem
                        },
                        lhs_node,
                        rhs_node,
                    )
                }
                BinaryOp::BitAnd | BinaryOp::LogicalAnd => {
                    builder.binary(BtorBinaryOp::And, lhs_node, rhs_node)
                }
                BinaryOp::BitOr | BinaryOp::LogicalOr => {
                    builder.binary(BtorBinaryOp::Or, lhs_node, rhs_node)
                }
                BinaryOp::BitXor => builder.binary(BtorBinaryOp::Xor, lhs_node, rhs_node),
                BinaryOp::Shl => builder.binary(BtorBinaryOp::Sll, lhs_node, rhs_node),
                BinaryOp::Shr => {
                    let scalar = ensure_scalar(lhs.ty).expect("shift lhs must be scalar");
                    builder.binary(
                        if scalar.signed {
                            BtorBinaryOp::Sra
                        } else {
                            BtorBinaryOp::Srl
                        },
                        lhs_node,
                        rhs_node,
                    )
                }
                BinaryOp::Eq => builder.binary(BtorBinaryOp::Eq, lhs_node, rhs_node),
                BinaryOp::Ne => {
                    let eq = builder.binary(BtorBinaryOp::Eq, lhs_node, rhs_node);
                    builder.unary(BtorUnaryOp::Not, eq)
                }
                BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                    let scalar = ensure_scalar(lhs.ty).expect("comparison lhs must be scalar");
                    let op = match (op, scalar.signed) {
                        (BinaryOp::Lt, true) => BtorBinaryOp::Slt,
                        (BinaryOp::Le, true) => BtorBinaryOp::Slte,
                        (BinaryOp::Gt, true) => BtorBinaryOp::Sgt,
                        (BinaryOp::Ge, true) => BtorBinaryOp::Sgte,
                        (BinaryOp::Lt, false) => BtorBinaryOp::Ult,
                        (BinaryOp::Le, false) => BtorBinaryOp::Ulte,
                        (BinaryOp::Gt, false) => BtorBinaryOp::Ugt,
                        (BinaryOp::Ge, false) => BtorBinaryOp::Ugte,
                        _ => unreachable!(),
                    };
                    builder.binary(op, lhs_node, rhs_node)
                }
            }
        }
    }
}

fn cast_node(
    value: NodeId,
    source: ExprType,
    target: ScalarType,
    builder: &mut BtorBuilder,
) -> NodeId {
    match source {
        ExprType::Bool => {
            if target.width == 1 {
                value
            } else {
                builder.uext(value, target.width - 1)
            }
        }
        ExprType::Scalar(source) => {
            if source.width == target.width {
                value
            } else if source.width < target.width {
                if source.signed {
                    builder.sext(value, target.width - source.width)
                } else {
                    builder.uext(value, target.width - source.width)
                }
            } else {
                builder.slice(value, target.width - 1, 0)
            }
        }
    }
}

fn bit_width_for(max_value: u64) -> u32 {
    let width = 64 - max_value.leading_zeros();
    width.max(1)
}

#[cfg(test)]
mod tests {
    use std::{fs, path::PathBuf};

    use super::{encode_btor2, lower_translation_unit};
    use zkpv_c0_parser::parse_translation_unit;

    const FIXTURES: &[&str] = &[
        "vendor/sv-benchmarks/c/infeasible-control-flow/unreach_branch1.c",
        "vendor/sv-benchmarks/c/infeasible-control-flow/unreach_branch3.c",
        "vendor/sv-benchmarks/c/infeasible-control-flow/conflict_branch1.c",
        "vendor/sv-benchmarks/c/loop-new/count_by_1.i",
        "vendor/sv-benchmarks/c/loop-new/count_by_2.i",
        "vendor/sv-benchmarks/c/loop-new/count_by_nondet.i",
        "vendor/sv-benchmarks/c/loop-new/gauss_sum.i",
        "vendor/sv-benchmarks/c/loop-simple/nested_1.c",
        "vendor/sv-benchmarks/c/loop-simple/nested_1b.c",
        "vendor/sv-benchmarks/c/bitvector/parity.i",
    ];

    #[test]
    fn lowers_count_by_1_to_btor2() {
        let source = r#"
            int main() {
                int i;
                for (i = 0; i < 10; i += 2) {
                }
                __VERIFIER_assert(i == 10);
                return 0;
            }
        "#;

        let unit = parse_translation_unit(source).unwrap();
        let lowered = lower_translation_unit(&unit).unwrap();
        let text = encode_btor2(&lowered).to_text();

        assert!(text.contains("state"));
        assert!(text.contains("next"));
        assert!(text.contains("bad"));
    }

    #[test]
    fn lowers_all_current_benchmarks() {
        let root =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../../benchmarks/svcomp-initial");

        for fixture in FIXTURES {
            let source = fs::read_to_string(root.join(fixture)).unwrap();
            let unit = parse_translation_unit(&source).unwrap();
            let lowered = lower_translation_unit(&unit)
                .unwrap_or_else(|err| panic!("failed to lower {fixture}: {err}"));
            let text = encode_btor2(&lowered).to_text();
            assert!(!text.is_empty(), "empty BTOR2 text for {fixture}");
        }
    }
}
