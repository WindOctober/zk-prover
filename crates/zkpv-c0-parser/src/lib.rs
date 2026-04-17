//! Parser for the restricted C0 language.

use winnow::ascii::multispace1;
use winnow::combinator::opt;
use winnow::error::{ContextError, ParserError as WinnowParserError};
use winnow::prelude::*;
use winnow::token::{one_of, take_till, take_until, take_while};

use thiserror::Error;
use zkpv_c0_ast::{
    AssignOp, BinaryOp, Block, Declarator, Expr, ForInit, Function, Item, OpaqueItem, Param,
    PostfixOp, Stmt, TranslationUnit, Type, UnaryOp, VarDeclStmt,
};

pub const CRATE_NAME: &str = "zkpv-c0-parser";

pub fn parse_translation_unit(source: &str) -> Result<TranslationUnit, ParseError> {
    let mut items = Vec::new();

    for raw_item in split_top_level_items(source) {
        let trimmed = raw_item.trim();
        if trimmed.is_empty() {
            continue;
        }

        if trimmed.contains('{') {
            match parse_function_item(trimmed) {
                Ok(function) => items.push(Item::Function(function)),
                Err(_) => items.push(Item::Opaque(build_opaque_item(trimmed))),
            }
        } else if trimmed.ends_with(';') && !trimmed.contains('(') {
            match parse_global_var_item(trimmed) {
                Ok(stmt) => items.push(Item::GlobalVar(stmt)),
                Err(_) => items.push(Item::Opaque(build_opaque_item(trimmed))),
            }
        } else {
            items.push(Item::Opaque(build_opaque_item(trimmed)));
        }
    }

    Ok(TranslationUnit { items })
}

fn parse_function_item(source: &str) -> Result<Function, ParseError> {
    let mut input = source;
    skip_trivia(&mut input).map_err(|_| ParseError::Unsupported("leading trivia"))?;
    let function = parse_function(&mut input).map_err(map_winnow_error)?;
    skip_trivia(&mut input).map_err(|_| ParseError::Unsupported("trailing trivia"))?;
    if input.is_empty() {
        Ok(function)
    } else {
        Err(ParseError::Unsupported(
            "trailing tokens after function body",
        ))
    }
}

fn parse_global_var_item(source: &str) -> Result<VarDeclStmt, ParseError> {
    let mut input = source;
    skip_trivia(&mut input).map_err(|_| ParseError::Unsupported("leading trivia"))?;
    while consume_keyword(&mut input, "extern") {}
    let stmt = parse_var_decl_stmt(&mut input).map_err(map_winnow_error)?;
    skip_trivia(&mut input).map_err(|_| ParseError::Unsupported("trailing trivia"))?;
    if consume_symbol(&mut input, ";") {
        skip_trivia(&mut input).map_err(|_| ParseError::Unsupported("trailing trivia"))?;
    }
    if input.is_empty() {
        Ok(stmt)
    } else {
        Err(ParseError::Unsupported("trailing tokens after global var"))
    }
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum ParseError {
    #[error("unexpected end of input while expecting {0}")]
    UnexpectedEof(&'static str),
    #[error("unsupported construct: {0}")]
    Unsupported(&'static str),
}

fn map_winnow_error(_error: winnow::error::ErrMode<ContextError>) -> ParseError {
    ParseError::Unsupported("winnow parser failed")
}

fn parse_function(input: &mut &str) -> ModalResult<Function> {
    while consume_keyword(input, "extern") {}

    let return_type = parse_type(input)?;
    let name = parse_ident(input)?;
    expect_symbol(input, "(")?;
    let params = parse_params(input)?;
    expect_symbol(input, ")")?;
    let body = parse_block(input)?;

    Ok(Function {
        return_type,
        name,
        params,
        body,
    })
}

fn parse_params(input: &mut &str) -> ModalResult<Vec<Param>> {
    if peek_symbol(input, ")") {
        return Ok(Vec::new());
    }

    let start = input.checkpoint();
    if consume_keyword(input, "void") && peek_symbol(input, ")") {
        return Ok(Vec::new());
    }
    input.reset(&start);

    let mut params = Vec::new();
    loop {
        let ty = parse_type(input)?;
        let name = if peek_ident(input) {
            Some(parse_ident(input)?)
        } else {
            None
        };
        params.push(Param { ty, name });

        if !consume_symbol(input, ",") {
            break;
        }
    }

    Ok(params)
}

fn parse_block(input: &mut &str) -> ModalResult<Block> {
    expect_symbol(input, "{")?;
    let mut stmts = Vec::new();
    while !peek_symbol(input, "}") {
        stmts.push(parse_stmt(input)?);
    }
    expect_symbol(input, "}")?;
    Ok(Block { stmts })
}

fn parse_stmt(input: &mut &str) -> ModalResult<Stmt> {
    if consume_symbol(input, ";") {
        return Ok(Stmt::Empty);
    }
    if peek_symbol(input, "{") {
        return Ok(Stmt::Block(parse_block(input)?));
    }
    if consume_keyword(input, "if") {
        expect_symbol(input, "(")?;
        let cond = parse_expr(input)?;
        expect_symbol(input, ")")?;
        let then_branch = Box::new(parse_stmt(input)?);
        let else_branch = if consume_keyword(input, "else") {
            Some(Box::new(parse_stmt(input)?))
        } else {
            None
        };
        return Ok(Stmt::If {
            cond,
            then_branch,
            else_branch,
        });
    }
    if consume_keyword(input, "while") {
        expect_symbol(input, "(")?;
        let cond = parse_expr(input)?;
        expect_symbol(input, ")")?;
        let body = Box::new(parse_stmt(input)?);
        return Ok(Stmt::While { cond, body });
    }
    if consume_keyword(input, "for") {
        expect_symbol(input, "(")?;
        let init = if consume_symbol(input, ";") {
            None
        } else if is_type_start(input) {
            let decl = parse_var_decl_stmt(input)?;
            expect_symbol(input, ";")?;
            Some(ForInit::VarDecl(decl))
        } else {
            let expr = parse_expr(input)?;
            expect_symbol(input, ";")?;
            Some(ForInit::Expr(expr))
        };

        let cond = if consume_symbol(input, ";") {
            None
        } else {
            let expr = parse_expr(input)?;
            expect_symbol(input, ";")?;
            Some(expr)
        };

        let step = if peek_symbol(input, ")") {
            None
        } else {
            Some(parse_expr(input)?)
        };

        expect_symbol(input, ")")?;
        let body = Box::new(parse_stmt(input)?);
        return Ok(Stmt::For {
            init,
            cond,
            step,
            body,
        });
    }
    if consume_keyword(input, "return") {
        if consume_symbol(input, ";") {
            return Ok(Stmt::Return(None));
        }
        let expr = parse_expr(input)?;
        expect_symbol(input, ";")?;
        return Ok(Stmt::Return(Some(expr)));
    }
    if is_type_start(input) {
        let decl = parse_var_decl_stmt(input)?;
        expect_symbol(input, ";")?;
        return Ok(Stmt::VarDecl(decl));
    }

    let expr = parse_expr(input)?;
    expect_symbol(input, ";")?;
    Ok(Stmt::Expr(expr))
}

fn parse_var_decl_stmt(input: &mut &str) -> ModalResult<VarDeclStmt> {
    let ty = parse_type(input)?;
    let mut declarators = Vec::new();

    loop {
        let name = parse_ident(input)?;
        let init = if consume_symbol(input, "=") {
            Some(parse_expr(input)?)
        } else {
            None
        };
        declarators.push(Declarator { name, init });
        if !consume_symbol(input, ",") {
            break;
        }
    }

    Ok(VarDeclStmt { ty, declarators })
}

fn parse_expr(input: &mut &str) -> ModalResult<Expr> {
    parse_assignment(input)
}

fn parse_assignment(input: &mut &str) -> ModalResult<Expr> {
    let lhs = parse_conditional(input)?;
    if consume_symbol(input, "=") {
        let rhs = parse_assignment(input)?;
        return Ok(Expr::Assign {
            op: AssignOp::Assign,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        });
    }
    if consume_symbol(input, "+=") {
        let rhs = parse_assignment(input)?;
        return Ok(Expr::Assign {
            op: AssignOp::AddAssign,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        });
    }
    if consume_symbol(input, "-=") {
        let rhs = parse_assignment(input)?;
        return Ok(Expr::Assign {
            op: AssignOp::SubAssign,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        });
    }
    Ok(lhs)
}

fn parse_conditional(input: &mut &str) -> ModalResult<Expr> {
    let cond = parse_logical_or(input)?;
    if !consume_symbol(input, "?") {
        return Ok(cond);
    }

    let then_expr = parse_expr(input)?;
    expect_symbol(input, ":")?;
    let else_expr = parse_conditional(input)?;
    Ok(Expr::Conditional {
        cond: Box::new(cond),
        then_expr: Box::new(then_expr),
        else_expr: Box::new(else_expr),
    })
}

fn parse_logical_or(input: &mut &str) -> ModalResult<Expr> {
    let mut expr = parse_logical_and(input)?;
    while consume_symbol(input, "||") {
        let rhs = parse_logical_and(input)?;
        expr = Expr::Binary {
            op: BinaryOp::LogicalOr,
            lhs: Box::new(expr),
            rhs: Box::new(rhs),
        };
    }
    Ok(expr)
}

fn parse_logical_and(input: &mut &str) -> ModalResult<Expr> {
    let mut expr = parse_bit_or(input)?;
    while consume_symbol(input, "&&") {
        let rhs = parse_bit_or(input)?;
        expr = Expr::Binary {
            op: BinaryOp::LogicalAnd,
            lhs: Box::new(expr),
            rhs: Box::new(rhs),
        };
    }
    Ok(expr)
}

fn parse_bit_or(input: &mut &str) -> ModalResult<Expr> {
    let mut expr = parse_bit_xor(input)?;
    while consume_symbol(input, "|") {
        let rhs = parse_bit_xor(input)?;
        expr = Expr::Binary {
            op: BinaryOp::BitOr,
            lhs: Box::new(expr),
            rhs: Box::new(rhs),
        };
    }
    Ok(expr)
}

fn parse_bit_xor(input: &mut &str) -> ModalResult<Expr> {
    let mut expr = parse_bit_and(input)?;
    while consume_symbol(input, "^") {
        let rhs = parse_bit_and(input)?;
        expr = Expr::Binary {
            op: BinaryOp::BitXor,
            lhs: Box::new(expr),
            rhs: Box::new(rhs),
        };
    }
    Ok(expr)
}

fn parse_bit_and(input: &mut &str) -> ModalResult<Expr> {
    let mut expr = parse_equality(input)?;
    while consume_symbol(input, "&") {
        let rhs = parse_equality(input)?;
        expr = Expr::Binary {
            op: BinaryOp::BitAnd,
            lhs: Box::new(expr),
            rhs: Box::new(rhs),
        };
    }
    Ok(expr)
}

fn parse_equality(input: &mut &str) -> ModalResult<Expr> {
    let mut expr = parse_relational(input)?;
    loop {
        let op = if consume_symbol(input, "==") {
            Some(BinaryOp::Eq)
        } else if consume_symbol(input, "!=") {
            Some(BinaryOp::Ne)
        } else {
            None
        };
        let Some(op) = op else { break };
        let rhs = parse_relational(input)?;
        expr = Expr::Binary {
            op,
            lhs: Box::new(expr),
            rhs: Box::new(rhs),
        };
    }
    Ok(expr)
}

fn parse_relational(input: &mut &str) -> ModalResult<Expr> {
    let mut expr = parse_shift(input)?;
    loop {
        let op = if consume_symbol(input, "<=") {
            Some(BinaryOp::Le)
        } else if consume_symbol(input, ">=") {
            Some(BinaryOp::Ge)
        } else if consume_symbol(input, "<") {
            Some(BinaryOp::Lt)
        } else if consume_symbol(input, ">") {
            Some(BinaryOp::Gt)
        } else {
            None
        };
        let Some(op) = op else { break };
        let rhs = parse_shift(input)?;
        expr = Expr::Binary {
            op,
            lhs: Box::new(expr),
            rhs: Box::new(rhs),
        };
    }
    Ok(expr)
}

fn parse_shift(input: &mut &str) -> ModalResult<Expr> {
    let mut expr = parse_additive(input)?;
    loop {
        let op = if consume_symbol(input, "<<") {
            Some(BinaryOp::Shl)
        } else if consume_symbol(input, ">>") {
            Some(BinaryOp::Shr)
        } else {
            None
        };
        let Some(op) = op else { break };
        let rhs = parse_additive(input)?;
        expr = Expr::Binary {
            op,
            lhs: Box::new(expr),
            rhs: Box::new(rhs),
        };
    }
    Ok(expr)
}

fn parse_additive(input: &mut &str) -> ModalResult<Expr> {
    let mut expr = parse_multiplicative(input)?;
    loop {
        let op = if consume_symbol(input, "+") {
            Some(BinaryOp::Add)
        } else if consume_symbol(input, "-") {
            Some(BinaryOp::Sub)
        } else {
            None
        };
        let Some(op) = op else { break };
        let rhs = parse_multiplicative(input)?;
        expr = Expr::Binary {
            op,
            lhs: Box::new(expr),
            rhs: Box::new(rhs),
        };
    }
    Ok(expr)
}

fn parse_multiplicative(input: &mut &str) -> ModalResult<Expr> {
    let mut expr = parse_unary(input)?;
    loop {
        let op = if consume_symbol(input, "*") {
            Some(BinaryOp::Mul)
        } else if consume_symbol(input, "/") {
            Some(BinaryOp::Div)
        } else if consume_symbol(input, "%") {
            Some(BinaryOp::Mod)
        } else {
            None
        };
        let Some(op) = op else { break };
        let rhs = parse_unary(input)?;
        expr = Expr::Binary {
            op,
            lhs: Box::new(expr),
            rhs: Box::new(rhs),
        };
    }
    Ok(expr)
}

fn parse_unary(input: &mut &str) -> ModalResult<Expr> {
    if consume_symbol(input, "++") {
        let expr = parse_unary(input)?;
        return Ok(Expr::Unary {
            op: UnaryOp::PreInc,
            expr: Box::new(expr),
        });
    }
    if consume_symbol(input, "--") {
        let expr = parse_unary(input)?;
        return Ok(Expr::Unary {
            op: UnaryOp::PreDec,
            expr: Box::new(expr),
        });
    }
    if consume_symbol(input, "+") {
        let expr = parse_unary(input)?;
        return Ok(Expr::Unary {
            op: UnaryOp::Plus,
            expr: Box::new(expr),
        });
    }
    if consume_symbol(input, "-") {
        let expr = parse_unary(input)?;
        return Ok(Expr::Unary {
            op: UnaryOp::Minus,
            expr: Box::new(expr),
        });
    }
    if consume_symbol(input, "!") {
        let expr = parse_unary(input)?;
        return Ok(Expr::Unary {
            op: UnaryOp::Not,
            expr: Box::new(expr),
        });
    }
    if consume_symbol(input, "~") {
        let expr = parse_unary(input)?;
        return Ok(Expr::Unary {
            op: UnaryOp::BitNot,
            expr: Box::new(expr),
        });
    }

    let start = input.checkpoint();
    if consume_symbol(input, "(") {
        if let Ok(ty) = parse_type(input) {
            if consume_symbol(input, ")") {
                let expr = parse_unary(input)?;
                return Ok(Expr::Cast {
                    ty,
                    expr: Box::new(expr),
                });
            }
        }
        input.reset(&start);
    }

    parse_postfix(input)
}

fn parse_postfix(input: &mut &str) -> ModalResult<Expr> {
    let mut expr = parse_primary(input)?;
    loop {
        if consume_symbol(input, "++") {
            expr = Expr::Postfix {
                op: PostfixOp::PostInc,
                expr: Box::new(expr),
            };
            continue;
        }
        if consume_symbol(input, "--") {
            expr = Expr::Postfix {
                op: PostfixOp::PostDec,
                expr: Box::new(expr),
            };
            continue;
        }
        break;
    }
    Ok(expr)
}

fn parse_primary(input: &mut &str) -> ModalResult<Expr> {
    let start = input.checkpoint();
    if let Ok(name) = parse_ident(input) {
        if consume_symbol(input, "(") {
            let mut args = Vec::new();
            if !consume_symbol(input, ")") {
                loop {
                    args.push(parse_expr(input)?);
                    if consume_symbol(input, ")") {
                        break;
                    }
                    expect_symbol(input, ",")?;
                }
            }
            return Ok(Expr::Call { callee: name, args });
        }
        return Ok(Expr::Ident(name));
    }
    input.reset(&start);

    if let Ok(value) = parse_int_literal(input) {
        return Ok(Expr::IntLiteral(value));
    }

    if consume_symbol(input, "(") {
        let expr = parse_expr(input)?;
        expect_symbol(input, ")")?;
        return Ok(expr);
    }

    Err(WinnowParserError::from_input(input))
}

fn parse_type(input: &mut &str) -> ModalResult<Type> {
    if consume_keyword(input, "void") {
        return Ok(Type::Void);
    }
    if consume_keyword(input, "unsigned") {
        if consume_keyword(input, "short") {
            let _ = consume_keyword(input, "int");
            return Ok(Type::UnsignedShort);
        }
        if consume_keyword(input, "long") {
            let _ = consume_keyword(input, "int");
            return Ok(Type::UnsignedLong);
        }
        if consume_keyword(input, "int") {
            return Ok(Type::UnsignedInt);
        }
        if consume_keyword(input, "char") {
            return Ok(Type::UnsignedChar);
        }
        return Ok(Type::UnsignedInt);
    }
    if consume_keyword(input, "signed") {
        if consume_keyword(input, "short") {
            let _ = consume_keyword(input, "int");
            return Ok(Type::Short);
        }
        if consume_keyword(input, "long") {
            let _ = consume_keyword(input, "int");
            return Ok(Type::Long);
        }
        if consume_keyword(input, "char") {
            return Ok(Type::SignedChar);
        }
        return Ok(Type::Int);
    }
    if consume_keyword(input, "short") {
        let _ = consume_keyword(input, "int");
        return Ok(Type::Short);
    }
    if consume_keyword(input, "long") {
        let _ = consume_keyword(input, "int");
        return Ok(Type::Long);
    }
    if consume_keyword(input, "int") {
        return Ok(Type::Int);
    }
    if consume_keyword(input, "char") {
        return Ok(Type::Char);
    }

    Err(WinnowParserError::from_input(input))
}

fn is_type_start(input: &mut &str) -> bool {
    peek_keyword(input, "void")
        || peek_keyword(input, "int")
        || peek_keyword(input, "short")
        || peek_keyword(input, "long")
        || peek_keyword(input, "unsigned")
        || peek_keyword(input, "signed")
        || peek_keyword(input, "char")
}

fn peek_ident(input: &mut &str) -> bool {
    let start = input.checkpoint();
    let ok = parse_ident(input).is_ok();
    input.reset(&start);
    ok
}

fn peek_keyword(input: &mut &str, keyword: &'static str) -> bool {
    let start = input.checkpoint();
    let ok = parse_keyword(input, keyword).is_ok();
    input.reset(&start);
    ok
}

fn peek_symbol(input: &mut &str, symbol: &'static str) -> bool {
    let start = input.checkpoint();
    let ok = parse_symbol(input, symbol).is_ok();
    input.reset(&start);
    ok
}

fn consume_keyword(input: &mut &str, keyword: &'static str) -> bool {
    let start = input.checkpoint();
    if parse_keyword(input, keyword).is_ok() {
        true
    } else {
        input.reset(&start);
        false
    }
}

fn consume_symbol(input: &mut &str, symbol: &'static str) -> bool {
    let start = input.checkpoint();
    if parse_symbol(input, symbol).is_ok() {
        true
    } else {
        input.reset(&start);
        false
    }
}

fn expect_symbol(input: &mut &str, symbol: &'static str) -> ModalResult<()> {
    parse_symbol(input, symbol).map(|_| ())
}

fn parse_keyword<'a>(input: &mut &'a str, mut keyword: &'static str) -> ModalResult<&'a str> {
    skip_trivia(input)?;
    let start = input.checkpoint();
    let matched = keyword.parse_next(input)?;
    if input.chars().next().is_some_and(is_ident_continue) {
        input.reset(&start);
        return Err(WinnowParserError::from_input(input));
    }
    skip_trivia(input)?;
    Ok(matched)
}

fn parse_symbol<'a>(input: &mut &'a str, mut symbol: &'static str) -> ModalResult<&'a str> {
    skip_trivia(input)?;
    let start = input.checkpoint();
    let matched = symbol.parse_next(input)?;
    if extends_to_longer_operator(symbol, input.chars().next()) {
        input.reset(&start);
        return Err(WinnowParserError::from_input(input));
    }
    skip_trivia(input)?;
    Ok(matched)
}

fn parse_ident(input: &mut &str) -> ModalResult<String> {
    skip_trivia(input)?;
    let start = input.checkpoint();
    let ident = (
        one_of(('_', 'a'..='z', 'A'..='Z')),
        take_while(0.., ('_', 'a'..='z', 'A'..='Z', '0'..='9')),
    )
        .take()
        .parse_next(input)?;
    if is_keyword(ident) {
        input.reset(&start);
        return Err(WinnowParserError::from_input(input));
    }
    skip_trivia(input)?;
    Ok(ident.to_owned())
}

fn parse_int_literal(input: &mut &str) -> ModalResult<String> {
    skip_trivia(input)?;
    let literal = (
        one_of('0'..='9'),
        take_while(0.., ('_', 'a'..='z', 'A'..='Z', '0'..='9')),
    )
        .take()
        .parse_next(input)?;
    skip_trivia(input)?;
    Ok(literal.to_owned())
}

fn skip_trivia(input: &mut &str) -> ModalResult<()> {
    loop {
        let before = *input;

        let _ = multispace1::<_, ContextError>.parse_next(input);
        let _ = opt(line_comment).parse_next(input);
        let _ = opt(block_comment).parse_next(input);

        if *input == before {
            return Ok(());
        }
    }
}

fn line_comment(input: &mut &str) -> ModalResult<()> {
    ("//", take_till(0.., '\n'), opt('\n'))
        .void()
        .parse_next(input)
}

fn block_comment(input: &mut &str) -> ModalResult<()> {
    ("/*", take_until(0.., "*/"), "*/").void().parse_next(input)
}

fn is_ident_continue(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphanumeric()
}

fn extends_to_longer_operator(symbol: &str, next: Option<char>) -> bool {
    matches!(
        (symbol, next),
        ("=", Some('='))
            | ("!", Some('='))
            | ("<", Some('='))
            | ("<", Some('<'))
            | (">", Some('='))
            | (">", Some('>'))
            | ("&", Some('&'))
            | ("|", Some('|'))
            | ("+", Some('+'))
            | ("+", Some('='))
            | ("-", Some('-'))
            | ("-", Some('='))
    )
}

fn is_keyword(ident: &str) -> bool {
    matches!(
        ident,
        "void"
            | "int"
            | "unsigned"
            | "signed"
            | "char"
            | "extern"
            | "if"
            | "else"
            | "while"
            | "for"
            | "return"
    )
}

fn build_opaque_item(raw: &str) -> OpaqueItem {
    let summary = raw
        .lines()
        .find(|line| !line.trim().is_empty())
        .map(|line| {
            let line = line.trim();
            if line.len() > 60 {
                format!("{}...", &line[..60])
            } else {
                line.to_owned()
            }
        })
        .unwrap_or_else(|| "opaque item".to_owned());

    OpaqueItem {
        summary,
        raw: raw.to_owned(),
    }
}

fn split_top_level_items(source: &str) -> Vec<&str> {
    let bytes = source.as_bytes();
    let mut start = 0usize;
    let mut index = 0usize;
    let mut paren_depth = 0usize;
    let mut brace_depth = 0usize;
    let mut items = Vec::new();

    while index < bytes.len() {
        let ch = bytes[index] as char;

        if ch == '/' && index + 1 < bytes.len() && bytes[index + 1] as char == '/' {
            index += 2;
            while index < bytes.len() && bytes[index] as char != '\n' {
                index += 1;
            }
            continue;
        }

        if ch == '/' && index + 1 < bytes.len() && bytes[index + 1] as char == '*' {
            index += 2;
            while index + 1 < bytes.len() {
                if bytes[index] as char == '*' && bytes[index + 1] as char == '/' {
                    index += 2;
                    break;
                }
                index += 1;
            }
            continue;
        }

        if ch == '"' {
            index += 1;
            while index < bytes.len() {
                let c = bytes[index] as char;
                if c == '\\' {
                    index += 2;
                    continue;
                }
                index += 1;
                if c == '"' {
                    break;
                }
            }
            continue;
        }

        match ch {
            '(' => paren_depth += 1,
            ')' => paren_depth = paren_depth.saturating_sub(1),
            '{' => brace_depth += 1,
            '}' => {
                brace_depth = brace_depth.saturating_sub(1);
                if brace_depth == 0 && paren_depth == 0 {
                    items.push(&source[start..=index]);
                    start = index + 1;
                }
            }
            ';' if brace_depth == 0 && paren_depth == 0 => {
                items.push(&source[start..=index]);
                start = index + 1;
            }
            _ => {}
        }

        index += 1;
    }

    if start < source.len() {
        items.push(&source[start..]);
    }

    items
}

#[cfg(test)]
mod tests {
    use super::parse_translation_unit;

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

    fn benchmark_root() -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../../../benchmarks/svcomp-initial")
    }

    #[test]
    fn parses_manifest_fixtures() {
        let root = benchmark_root();

        for relative_path in FIXTURES {
            let source = std::fs::read_to_string(root.join(relative_path)).unwrap();
            let unit = parse_translation_unit(&source).unwrap();
            assert!(
                unit.main_function().is_some(),
                "expected main function in {relative_path}"
            );

            let pretty = unit.to_string();
            let reparsed = parse_translation_unit(&pretty).unwrap();
            assert!(
                reparsed.main_function().is_some(),
                "pretty-printed program lost main function in {relative_path}"
            );
        }
    }
}
