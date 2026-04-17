//! AST for the restricted C0 input language.

use core::fmt;
use serde::{Deserialize, Serialize};

pub const CRATE_NAME: &str = "zkpv-c0-ast";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TranslationUnit {
    pub items: Vec<Item>,
}

impl TranslationUnit {
    pub fn main_function(&self) -> Option<&Function> {
        self.items.iter().find_map(|item| match item {
            Item::Function(function) if function.name == "main" => Some(function),
            _ => None,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Item {
    Function(Function),
    GlobalVar(VarDeclStmt),
    Opaque(OpaqueItem),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpaqueItem {
    pub summary: String,
    pub raw: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Function {
    pub return_type: Type,
    pub name: String,
    pub params: Vec<Param>,
    pub body: Block,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Param {
    pub ty: Type,
    pub name: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Block {
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Stmt {
    Block(Block),
    VarDecl(VarDeclStmt),
    If {
        cond: Expr,
        then_branch: Box<Stmt>,
        else_branch: Option<Box<Stmt>>,
    },
    While {
        cond: Expr,
        body: Box<Stmt>,
    },
    For {
        init: Option<ForInit>,
        cond: Option<Expr>,
        step: Option<Expr>,
        body: Box<Stmt>,
    },
    Return(Option<Expr>),
    Expr(Expr),
    Empty,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ForInit {
    VarDecl(VarDeclStmt),
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VarDeclStmt {
    pub ty: Type,
    pub declarators: Vec<Declarator>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Declarator {
    pub name: String,
    pub init: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Expr {
    Ident(String),
    IntLiteral(String),
    Call {
        callee: String,
        args: Vec<Expr>,
    },
    Conditional {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    Cast {
        ty: Type,
        expr: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Assign {
        op: AssignOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Postfix {
        op: PostfixOp,
        expr: Box<Expr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnaryOp {
    Plus,
    Minus,
    Not,
    BitNot,
    PreInc,
    PreDec,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PostfixOp {
    PostInc,
    PostDec,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    LogicalAnd,
    LogicalOr,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AssignOp {
    Assign,
    AddAssign,
    SubAssign,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Type {
    Void,
    Int,
    UnsignedInt,
    Short,
    UnsignedShort,
    Long,
    UnsignedLong,
    Char,
    SignedChar,
    UnsignedChar,
}

impl fmt::Display for TranslationUnit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, item) in self.items.iter().enumerate() {
            if index > 0 {
                writeln!(f)?;
            }
            item.fmt_with_indent(f, 0)?;
        }
        Ok(())
    }
}

impl Item {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        match self {
            Item::Function(function) => function.fmt_with_indent(f, indent),
            Item::GlobalVar(stmt) => stmt.fmt_with_indent(f, indent),
            Item::Opaque(item) => {
                writeln!(f, "{}/* opaque: {} */", spaces(indent), item.summary)
            }
        }
    }
}

impl Function {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        write!(f, "{}{} {}(", spaces(indent), self.return_type, self.name)?;
        for (index, param) in self.params.iter().enumerate() {
            if index > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", param.ty)?;
            if let Some(name) = &param.name {
                write!(f, " {}", name)?;
            }
        }
        writeln!(f, ") {{")?;
        for stmt in &self.body.stmts {
            stmt.fmt_with_indent(f, indent + 4)?;
        }
        writeln!(f, "{}}}", spaces(indent))
    }
}

impl Stmt {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        match self {
            Stmt::Block(block) => {
                writeln!(f, "{}{{", spaces(indent))?;
                for stmt in &block.stmts {
                    stmt.fmt_with_indent(f, indent + 4)?;
                }
                writeln!(f, "{}}}", spaces(indent))
            }
            Stmt::VarDecl(stmt) => {
                write!(f, "{}{}", spaces(indent), stmt.ty)?;
                for (index, declarator) in stmt.declarators.iter().enumerate() {
                    if index == 0 {
                        write!(f, " ")?;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", declarator.name)?;
                    if let Some(init) = &declarator.init {
                        write!(f, " = {}", init)?;
                    }
                }
                writeln!(f, ";")
            }
            Stmt::If {
                cond,
                then_branch,
                else_branch,
            } => {
                write!(f, "{}if ({}) ", spaces(indent), cond)?;
                then_branch.fmt_compact_or_block(f, indent)?;
                if let Some(else_branch) = else_branch {
                    write!(f, "{}else ", spaces(indent))?;
                    else_branch.fmt_compact_or_block(f, indent)?;
                }
                Ok(())
            }
            Stmt::While { cond, body } => {
                write!(f, "{}while ({}) ", spaces(indent), cond)?;
                body.fmt_compact_or_block(f, indent)
            }
            Stmt::For {
                init,
                cond,
                step,
                body,
            } => {
                write!(f, "{}for (", spaces(indent))?;
                if let Some(init) = init {
                    match init {
                        ForInit::VarDecl(decl) => {
                            write!(f, "{}", decl.ty)?;
                            for (index, declarator) in decl.declarators.iter().enumerate() {
                                if index == 0 {
                                    write!(f, " ")?;
                                } else {
                                    write!(f, ", ")?;
                                }
                                write!(f, "{}", declarator.name)?;
                                if let Some(init) = &declarator.init {
                                    write!(f, " = {}", init)?;
                                }
                            }
                        }
                        ForInit::Expr(expr) => write!(f, "{expr}")?,
                    }
                }
                write!(f, "; ")?;
                if let Some(cond) = cond {
                    write!(f, "{cond}")?;
                }
                write!(f, "; ")?;
                if let Some(step) = step {
                    write!(f, "{step}")?;
                }
                write!(f, ") ")?;
                body.fmt_compact_or_block(f, indent)
            }
            Stmt::Return(expr) => {
                if let Some(expr) = expr {
                    writeln!(f, "{}return {};", spaces(indent), expr)
                } else {
                    writeln!(f, "{}return;", spaces(indent))
                }
            }
            Stmt::Expr(expr) => writeln!(f, "{}{};", spaces(indent), expr),
            Stmt::Empty => writeln!(f, "{};", spaces(indent)),
        }
    }

    fn fmt_compact_or_block(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        match self {
            Stmt::Block(_) => self.fmt_with_indent(f, indent),
            _ => {
                writeln!(f)?;
                self.fmt_with_indent(f, indent + 4)
            }
        }
    }
}

impl VarDeclStmt {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        write!(f, "{}{}", spaces(indent), self.ty)?;
        for (index, declarator) in self.declarators.iter().enumerate() {
            if index == 0 {
                write!(f, " ")?;
            } else {
                write!(f, ", ")?;
            }
            write!(f, "{}", declarator.name)?;
            if let Some(init) = &declarator.init {
                write!(f, " = {}", init)?;
            }
        }
        writeln!(f, ";")
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_prec(f, 0)
    }
}

impl Expr {
    fn fmt_with_prec(&self, f: &mut fmt::Formatter<'_>, parent_prec: u8) -> fmt::Result {
        let my_prec = self.precedence();
        let needs_paren = my_prec < parent_prec;
        if needs_paren {
            write!(f, "(")?;
        }
        match self {
            Expr::Ident(name) => write!(f, "{name}")?,
            Expr::IntLiteral(value) => write!(f, "{value}")?,
            Expr::Call { callee, args } => {
                write!(f, "{callee}(")?;
                for (index, arg) in args.iter().enumerate() {
                    if index > 0 {
                        write!(f, ", ")?;
                    }
                    arg.fmt_with_prec(f, 0)?;
                }
                write!(f, ")")?;
            }
            Expr::Conditional {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.fmt_with_prec(f, my_prec)?;
                write!(f, " ? ")?;
                then_expr.fmt_with_prec(f, my_prec)?;
                write!(f, " : ")?;
                else_expr.fmt_with_prec(f, my_prec)?;
            }
            Expr::Cast { ty, expr } => {
                write!(f, "({}) ", ty)?;
                expr.fmt_with_prec(f, my_prec)?;
            }
            Expr::Unary { op, expr } => {
                write!(f, "{op}")?;
                expr.fmt_with_prec(f, my_prec)?;
            }
            Expr::Binary { op, lhs, rhs } => {
                lhs.fmt_with_prec(f, my_prec)?;
                write!(f, " {op} ")?;
                rhs.fmt_with_prec(f, my_prec + 1)?;
            }
            Expr::Assign { op, lhs, rhs } => {
                lhs.fmt_with_prec(f, my_prec)?;
                write!(f, " {op} ")?;
                rhs.fmt_with_prec(f, my_prec)?;
            }
            Expr::Postfix { op, expr } => {
                expr.fmt_with_prec(f, my_prec)?;
                write!(f, "{op}")?;
            }
        }
        if needs_paren {
            write!(f, ")")?;
        }
        Ok(())
    }

    fn precedence(&self) -> u8 {
        match self {
            Expr::Assign { .. } => 1,
            Expr::Conditional { .. } => 2,
            Expr::Binary {
                op: BinaryOp::LogicalOr,
                ..
            } => 3,
            Expr::Binary {
                op: BinaryOp::LogicalAnd,
                ..
            } => 4,
            Expr::Binary {
                op: BinaryOp::BitOr,
                ..
            } => 5,
            Expr::Binary {
                op: BinaryOp::BitXor,
                ..
            } => 6,
            Expr::Binary {
                op: BinaryOp::BitAnd,
                ..
            } => 7,
            Expr::Binary {
                op: BinaryOp::Eq | BinaryOp::Ne,
                ..
            } => 8,
            Expr::Binary {
                op: BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge,
                ..
            } => 9,
            Expr::Binary {
                op: BinaryOp::Shl | BinaryOp::Shr,
                ..
            } => 10,
            Expr::Binary {
                op: BinaryOp::Add | BinaryOp::Sub,
                ..
            } => 11,
            Expr::Binary {
                op: BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod,
                ..
            } => 12,
            Expr::Cast { .. } | Expr::Unary { .. } => 13,
            Expr::Postfix { .. } | Expr::Call { .. } => 14,
            Expr::Ident(_) | Expr::IntLiteral(_) => 15,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Type::Void => "void",
            Type::Int => "int",
            Type::UnsignedInt => "unsigned int",
            Type::Short => "short",
            Type::UnsignedShort => "unsigned short",
            Type::Long => "long",
            Type::UnsignedLong => "unsigned long",
            Type::Char => "char",
            Type::SignedChar => "signed char",
            Type::UnsignedChar => "unsigned char",
        };
        write!(f, "{text}")
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            UnaryOp::Plus => "+",
            UnaryOp::Minus => "-",
            UnaryOp::Not => "!",
            UnaryOp::BitNot => "~",
            UnaryOp::PreInc => "++",
            UnaryOp::PreDec => "--",
        };
        write!(f, "{text}")
    }
}

impl fmt::Display for PostfixOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            PostfixOp::PostInc => "++",
            PostfixOp::PostDec => "--",
        };
        write!(f, "{text}")
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            BinaryOp::Add => "+",
            BinaryOp::Sub => "-",
            BinaryOp::Mul => "*",
            BinaryOp::Div => "/",
            BinaryOp::Mod => "%",
            BinaryOp::Lt => "<",
            BinaryOp::Le => "<=",
            BinaryOp::Gt => ">",
            BinaryOp::Ge => ">=",
            BinaryOp::Eq => "==",
            BinaryOp::Ne => "!=",
            BinaryOp::LogicalAnd => "&&",
            BinaryOp::LogicalOr => "||",
            BinaryOp::BitAnd => "&",
            BinaryOp::BitOr => "|",
            BinaryOp::BitXor => "^",
            BinaryOp::Shl => "<<",
            BinaryOp::Shr => ">>",
        };
        write!(f, "{text}")
    }
}

impl fmt::Display for AssignOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            AssignOp::Assign => "=",
            AssignOp::AddAssign => "+=",
            AssignOp::SubAssign => "-=",
        };
        write!(f, "{text}")
    }
}

fn spaces(indent: usize) -> &'static str {
    const SPACES: &str = "                                                                ";
    &SPACES[..indent.min(SPACES.len())]
}
