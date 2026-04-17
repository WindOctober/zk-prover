use std::collections::{BTreeMap, BTreeSet};

use crate::backend::cnf::{CnfBuilder, Lit};
use crate::frontend::ir::{
    Action, BasicBlock, ExprKind, ExprType, ScalarType, Terminator, TypedExpr, VerificationProgram,
};
use crate::{EncodeError, EncodedCnf};
use zkpv_c0_ast::{BinaryOp, UnaryOp};

#[derive(Debug, Clone)]
struct IncomingState {
    guard: Lit,
    vars: BTreeMap<String, Vec<Lit>>,
}

#[derive(Debug, Default)]
struct InputCache {
    symbols: BTreeMap<String, Vec<Lit>>,
}

pub fn encode_program_to_cnf(
    program: &VerificationProgram,
    steps: u32,
) -> Result<EncodedCnf, EncodeError> {
    let mut builder = CnfBuilder::default();
    let mut inputs = InputCache::default();
    let blocks = program
        .blocks
        .iter()
        .map(|block| (block.id, block))
        .collect::<BTreeMap<_, _>>();
    let live_in = compute_live_in(program, &blocks)?;

    let mut pending = BTreeMap::<u32, Vec<IncomingState>>::new();
    pending
        .entry(program.entry_block)
        .or_default()
        .push(IncomingState {
            guard: builder.const_true(),
            vars: trim_state(
                zero_state(program, &builder),
                &live_in[&program.entry_block],
            ),
        });

    let mut bad_paths = Vec::new();
    for block_id in topological_order(program, &blocks)? {
        let Some(block) = blocks.get(&block_id).copied() else {
            continue;
        };
        let Some(incoming) = pending.remove(&block_id) else {
            continue;
        };
        let state = merge_states(&live_in[&block_id], incoming, &mut builder);
        process_block(
            program,
            &blocks,
            &live_in,
            block,
            state,
            &mut pending,
            &mut bad_paths,
            &mut inputs,
            &mut builder,
        )?;
    }

    let bad = builder.or_all(bad_paths);
    builder.add_unit(bad);

    let cnf = builder.finish();
    Ok(EncodedCnf {
        steps,
        blocks: program.blocks.len() as u32,
        program_vars: program.variables.len() as u32,
        nondet_symbols: inputs.symbols.len() as u32,
        cnf,
    })
}

fn zero_state(program: &VerificationProgram, builder: &CnfBuilder) -> BTreeMap<String, Vec<Lit>> {
    program
        .variables
        .iter()
        .map(|variable| {
            (
                variable.name.clone(),
                builder.const_bitvec(variable.ty.width, 0),
            )
        })
        .collect()
}

fn topological_order(
    program: &VerificationProgram,
    blocks: &BTreeMap<u32, &BasicBlock>,
) -> Result<Vec<u32>, EncodeError> {
    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut order = Vec::new();

    fn visit(
        program: &VerificationProgram,
        blocks: &BTreeMap<u32, &BasicBlock>,
        block_id: u32,
        visiting: &mut BTreeSet<u32>,
        visited: &mut BTreeSet<u32>,
        order: &mut Vec<u32>,
    ) -> Result<(), EncodeError> {
        if block_id == program.exit_block || block_id == program.error_block {
            return Ok(());
        }
        if visited.contains(&block_id) {
            return Ok(());
        }
        if !visiting.insert(block_id) {
            return Err(EncodeError::Unsupported(
                "cyclic control-flow requires an explicit loop/recursion handling strategy"
                    .to_owned(),
            ));
        }

        let Some(block) = blocks.get(&block_id).copied() else {
            return Ok(());
        };

        match &block.terminator {
            Terminator::Goto(target) => {
                visit(program, blocks, *target, visiting, visited, order)?;
            }
            Terminator::Branch {
                then_block,
                else_block,
                ..
            } => {
                visit(program, blocks, *then_block, visiting, visited, order)?;
                visit(program, blocks, *else_block, visiting, visited, order)?;
            }
            Terminator::Return => {}
        }

        visiting.remove(&block_id);
        visited.insert(block_id);
        order.push(block_id);
        Ok(())
    }

    visit(
        program,
        blocks,
        program.entry_block,
        &mut visiting,
        &mut visited,
        &mut order,
    )?;
    order.reverse();
    Ok(order)
}

fn merge_states(
    live_vars: &BTreeSet<String>,
    incoming: Vec<IncomingState>,
    builder: &mut CnfBuilder,
) -> IncomingState {
    if incoming.len() == 1 {
        return incoming.into_iter().next().expect("single incoming state");
    }

    let guard = builder.or_all(incoming.iter().map(|state| state.guard));
    let mut vars = BTreeMap::new();

    for variable in live_vars {
        let first = &incoming[0].vars[variable];
        if incoming.iter().all(|state| state.vars[variable] == *first) {
            vars.insert(variable.clone(), first.clone());
            continue;
        }

        let width = first.len() as u32;
        let mut merged = builder.const_bitvec(width, 0);
        for state in incoming.iter().rev() {
            merged = guarded_bits(state.guard, &state.vars[variable], &merged, builder);
        }
        vars.insert(variable.clone(), merged);
    }

    IncomingState { guard, vars }
}

fn process_block(
    program: &VerificationProgram,
    blocks: &BTreeMap<u32, &BasicBlock>,
    live_in: &BTreeMap<u32, BTreeSet<String>>,
    block: &BasicBlock,
    state: IncomingState,
    pending: &mut BTreeMap<u32, Vec<IncomingState>>,
    bad_paths: &mut Vec<Lit>,
    inputs: &mut InputCache,
    builder: &mut CnfBuilder,
) -> Result<(), EncodeError> {
    let mut guard = state.guard;
    let mut env = state.vars;
    let action_live_after = block_action_live_after(
        block,
        &live_out_for_block(program, blocks, live_in, block.id),
    );

    for (action, live_after) in block.actions.iter().zip(action_live_after.iter()) {
        match action {
            Action::Assign { target, value } => {
                if !live_after.contains(target) {
                    continue;
                }
                let computed = encode_expr(value, &env, inputs, builder)?;
                env.insert(target.clone(), computed);
            }
            Action::Assert(cond) => {
                let cond_lit = as_bool_lit(cond, &env, inputs, builder)?;
                record_guarded_bad(guard, builder.not(cond_lit), bad_paths, builder);
                guard = guarded_and(guard, cond_lit, builder);
            }
        }
    }

    match &block.terminator {
        Terminator::Goto(target) => {
            enqueue_successor(
                program, blocks, live_in, *target, guard, env, pending, bad_paths,
            );
        }
        Terminator::Return => {}
        Terminator::Branch {
            cond,
            then_block,
            else_block,
        } => {
            let cond_lit = as_bool_lit(cond, &env, inputs, builder)?;
            let then_guard = guarded_and(guard, cond_lit, builder);
            let else_guard = guarded_and(guard, builder.not(cond_lit), builder);
            enqueue_successor(
                program,
                blocks,
                live_in,
                *then_block,
                then_guard,
                env.clone(),
                pending,
                bad_paths,
            );
            enqueue_successor(
                program,
                blocks,
                live_in,
                *else_block,
                else_guard,
                env,
                pending,
                bad_paths,
            );
        }
    }

    Ok(())
}

fn enqueue_successor(
    program: &VerificationProgram,
    blocks: &BTreeMap<u32, &BasicBlock>,
    live_in: &BTreeMap<u32, BTreeSet<String>>,
    target: u32,
    guard: Lit,
    vars: BTreeMap<String, Vec<Lit>>,
    pending: &mut BTreeMap<u32, Vec<IncomingState>>,
    bad_paths: &mut Vec<Lit>,
) {
    if guard == 0 {
        return;
    }
    let target = canonical_target(program, blocks, target);
    if target == program.exit_block {
        return;
    }
    if target == program.error_block {
        if guard > 0 || guard < 0 {
            bad_paths.push(guard);
        }
        return;
    }

    let vars = trim_state(vars, &live_in[&target]);
    pending
        .entry(target)
        .or_default()
        .push(IncomingState { guard, vars });
}

fn canonical_target(
    program: &VerificationProgram,
    blocks: &BTreeMap<u32, &BasicBlock>,
    mut target: u32,
) -> u32 {
    let mut seen = BTreeSet::new();

    loop {
        if target == program.exit_block || target == program.error_block {
            return target;
        }
        if !seen.insert(target) {
            return target;
        }

        let Some(block) = blocks.get(&target).copied() else {
            return target;
        };

        if block.actions.is_empty() {
            match block.terminator {
                Terminator::Goto(next) => {
                    target = next;
                    continue;
                }
                Terminator::Return => return program.exit_block,
                Terminator::Branch { .. } => {}
            }
        }

        return target;
    }
}

fn record_guarded_bad(guard: Lit, bad: Lit, bad_paths: &mut Vec<Lit>, builder: &mut CnfBuilder) {
    let guarded = guarded_and(guard, bad, builder);
    if guarded != builder.const_false() {
        bad_paths.push(guarded);
    }
}

fn guarded_and(lhs: Lit, rhs: Lit, builder: &mut CnfBuilder) -> Lit {
    if lhs == builder.const_true() {
        rhs
    } else if rhs == builder.const_true() {
        lhs
    } else if lhs == builder.const_false() || rhs == builder.const_false() {
        builder.const_false()
    } else {
        builder.and(lhs, rhs)
    }
}

fn guarded_bits(
    cond: Lit,
    then_bits: &[Lit],
    else_bits: &[Lit],
    builder: &mut CnfBuilder,
) -> Vec<Lit> {
    if then_bits == else_bits {
        return then_bits.to_vec();
    }
    if cond == builder.const_true() {
        then_bits.to_vec()
    } else if cond == builder.const_false() {
        else_bits.to_vec()
    } else {
        bv_ite(cond, then_bits, else_bits, builder)
    }
}

fn compute_live_in(
    program: &VerificationProgram,
    blocks: &BTreeMap<u32, &BasicBlock>,
) -> Result<BTreeMap<u32, BTreeSet<String>>, EncodeError> {
    let order = topological_order(program, blocks)?;
    let mut live_in = BTreeMap::<u32, BTreeSet<String>>::new();

    for block_id in order.into_iter().rev() {
        let block = blocks[&block_id];
        let mut live = live_out_for_block(program, blocks, &live_in, block_id);

        match &block.terminator {
            Terminator::Goto(_) | Terminator::Return => {}
            Terminator::Branch { cond, .. } => collect_expr_vars(cond, &mut live),
        }

        for action in block.actions.iter().rev() {
            match action {
                Action::Assign { target, value } => {
                    if live.remove(target) {
                        collect_expr_vars(value, &mut live);
                    }
                }
                Action::Assert(cond) => collect_expr_vars(cond, &mut live),
            }
        }

        live_in.insert(block_id, live);
    }

    Ok(live_in)
}

fn live_out_for_block(
    program: &VerificationProgram,
    blocks: &BTreeMap<u32, &BasicBlock>,
    live_in: &BTreeMap<u32, BTreeSet<String>>,
    block_id: u32,
) -> BTreeSet<String> {
    let block = blocks[&block_id];
    match &block.terminator {
        Terminator::Goto(target) => successor_live(program, blocks, live_in, *target),
        Terminator::Return => BTreeSet::new(),
        Terminator::Branch {
            then_block,
            else_block,
            ..
        } => {
            let mut live = successor_live(program, blocks, live_in, *then_block);
            live.extend(successor_live(program, blocks, live_in, *else_block));
            live
        }
    }
}

fn successor_live(
    program: &VerificationProgram,
    blocks: &BTreeMap<u32, &BasicBlock>,
    live_in: &BTreeMap<u32, BTreeSet<String>>,
    target: u32,
) -> BTreeSet<String> {
    let target = canonical_target(program, blocks, target);
    if target == program.exit_block || target == program.error_block {
        BTreeSet::new()
    } else {
        live_in.get(&target).cloned().unwrap_or_default()
    }
}

fn block_action_live_after(
    block: &BasicBlock,
    block_live_out: &BTreeSet<String>,
) -> Vec<BTreeSet<String>> {
    let mut live = block_live_out.clone();
    if let Terminator::Branch { cond, .. } = &block.terminator {
        collect_expr_vars(cond, &mut live);
    }
    let mut live_after = vec![BTreeSet::new(); block.actions.len()];

    for (index, action) in block.actions.iter().enumerate().rev() {
        live_after[index] = live.clone();
        match action {
            Action::Assign { target, value } => {
                if live.remove(target) {
                    collect_expr_vars(value, &mut live);
                }
            }
            Action::Assert(cond) => collect_expr_vars(cond, &mut live),
        }
    }

    live_after
}

fn trim_state(
    vars: BTreeMap<String, Vec<Lit>>,
    live_vars: &BTreeSet<String>,
) -> BTreeMap<String, Vec<Lit>> {
    vars.into_iter()
        .filter(|(name, _)| live_vars.contains(name))
        .collect()
}

fn collect_expr_vars(expr: &TypedExpr, out: &mut BTreeSet<String>) {
    match &expr.kind {
        ExprKind::Var(name) => {
            out.insert(name.clone());
        }
        ExprKind::Const(_) | ExprKind::Nondet { .. } => {}
        ExprKind::Cast { expr, .. } | ExprKind::Unary { expr, .. } => collect_expr_vars(expr, out),
        ExprKind::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr_vars(cond, out);
            collect_expr_vars(then_expr, out);
            collect_expr_vars(else_expr, out);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_expr_vars(lhs, out);
            collect_expr_vars(rhs, out);
        }
    }
}

fn encode_expr(
    expr: &TypedExpr,
    env: &BTreeMap<String, Vec<Lit>>,
    inputs: &mut InputCache,
    builder: &mut CnfBuilder,
) -> Result<Vec<Lit>, EncodeError> {
    match &expr.kind {
        ExprKind::Var(name) => Ok(env[name].clone()),
        ExprKind::Const(value) => Ok(match expr.ty {
            ExprType::Bool => vec![if (*value & 1) == 1 {
                builder.const_true()
            } else {
                builder.const_false()
            }],
            ExprType::Scalar(ty) => builder.const_bitvec(ty.width, *value),
        }),
        ExprKind::Nondet { symbol } => {
            let width = match expr.ty {
                ExprType::Bool => 1,
                ExprType::Scalar(ty) => ty.width,
            };
            if let Some(bits) = inputs.symbols.get(symbol) {
                return Ok(bits.clone());
            }

            let bits = (0..width).map(|_| builder.fresh_lit()).collect::<Vec<_>>();
            inputs.symbols.insert(symbol.clone(), bits.clone());
            Ok(bits)
        }
        ExprKind::Cast {
            expr: inner,
            target,
        } => {
            let value = encode_expr(inner, env, inputs, builder)?;
            Ok(cast_bits(&value, inner.ty, *target, builder))
        }
        ExprKind::Unary { op, expr: inner } => {
            let value = encode_expr(inner, env, inputs, builder)?;
            match op {
                UnaryOp::Plus => Ok(value),
                UnaryOp::Minus => Ok(bv_neg(&value, builder)),
                UnaryOp::BitNot => Ok(value.iter().map(|bit| builder.not(*bit)).collect()),
                UnaryOp::Not => {
                    let as_bool = as_bool_value(&value, expr.ty, builder);
                    Ok(vec![builder.not(as_bool)])
                }
                UnaryOp::PreInc | UnaryOp::PreDec => Err(EncodeError::Unsupported(
                    "prefix update expressions should not survive normalization".to_owned(),
                )),
            }
        }
        ExprKind::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            let cond_lit = as_bool_lit(cond, env, inputs, builder)?;
            let then_bits = encode_expr(then_expr, env, inputs, builder)?;
            let else_bits = encode_expr(else_expr, env, inputs, builder)?;
            Ok(guarded_bits(cond_lit, &then_bits, &else_bits, builder))
        }
        ExprKind::Binary { op, lhs, rhs } => {
            let lhs_bits = encode_expr(lhs, env, inputs, builder)?;
            let rhs_bits = encode_expr(rhs, env, inputs, builder)?;
            match op {
                BinaryOp::Add => Ok(bv_add(&lhs_bits, &rhs_bits, builder)),
                BinaryOp::Sub => Ok(bv_sub(&lhs_bits, &rhs_bits, builder)),
                BinaryOp::Mul => Ok(bv_mul(&lhs_bits, &rhs_bits, builder)),
                BinaryOp::Div | BinaryOp::Mod => Err(EncodeError::Unsupported(
                    "division and modulo are not supported by the current CNF encoder".to_owned(),
                )),
                BinaryOp::BitAnd | BinaryOp::LogicalAnd => Ok(lhs_bits
                    .iter()
                    .zip(rhs_bits.iter())
                    .map(|(lhs, rhs)| builder.and(*lhs, *rhs))
                    .collect()),
                BinaryOp::BitOr | BinaryOp::LogicalOr => Ok(lhs_bits
                    .iter()
                    .zip(rhs_bits.iter())
                    .map(|(lhs, rhs)| builder.or(*lhs, *rhs))
                    .collect()),
                BinaryOp::BitXor => Ok(lhs_bits
                    .iter()
                    .zip(rhs_bits.iter())
                    .map(|(lhs, rhs)| builder.xor(*lhs, *rhs))
                    .collect()),
                BinaryOp::Shl => Ok(bv_shift_left(&lhs_bits, &rhs_bits, builder)),
                BinaryOp::Shr => {
                    let scalar = scalar_type(lhs.ty)?;
                    Ok(bv_shift_right(&lhs_bits, &rhs_bits, scalar.signed, builder))
                }
                BinaryOp::Eq => Ok(vec![eq_bitvec(&lhs_bits, &rhs_bits, builder)]),
                BinaryOp::Ne => {
                    let eq = eq_bitvec(&lhs_bits, &rhs_bits, builder);
                    Ok(vec![builder.not(eq)])
                }
                BinaryOp::Lt => {
                    let scalar = scalar_type(lhs.ty)?;
                    Ok(vec![bv_lt(&lhs_bits, &rhs_bits, scalar.signed, builder)])
                }
                BinaryOp::Le => {
                    let scalar = scalar_type(lhs.ty)?;
                    let lt = bv_lt(&lhs_bits, &rhs_bits, scalar.signed, builder);
                    let eq = eq_bitvec(&lhs_bits, &rhs_bits, builder);
                    Ok(vec![builder.or(lt, eq)])
                }
                BinaryOp::Gt => {
                    let scalar = scalar_type(lhs.ty)?;
                    Ok(vec![bv_lt(&rhs_bits, &lhs_bits, scalar.signed, builder)])
                }
                BinaryOp::Ge => {
                    let scalar = scalar_type(lhs.ty)?;
                    let gt = bv_lt(&rhs_bits, &lhs_bits, scalar.signed, builder);
                    let eq = eq_bitvec(&lhs_bits, &rhs_bits, builder);
                    Ok(vec![builder.or(gt, eq)])
                }
            }
        }
    }
}

fn as_bool_lit(
    expr: &TypedExpr,
    env: &BTreeMap<String, Vec<Lit>>,
    inputs: &mut InputCache,
    builder: &mut CnfBuilder,
) -> Result<Lit, EncodeError> {
    let bits = encode_expr(expr, env, inputs, builder)?;
    Ok(as_bool_value(&bits, expr.ty, builder))
}

fn as_bool_value(bits: &[Lit], ty: ExprType, builder: &mut CnfBuilder) -> Lit {
    match ty {
        ExprType::Bool => bits[0],
        ExprType::Scalar(_) => builder.or_all(bits.iter().copied()),
    }
}

fn scalar_type(ty: ExprType) -> Result<ScalarType, EncodeError> {
    match ty {
        ExprType::Scalar(ty) => Ok(ty),
        ExprType::Bool => Err(EncodeError::Unsupported(
            "boolean expression used where scalar semantics were required".to_owned(),
        )),
    }
}

fn eq_bitvec(lhs: &[Lit], rhs: &[Lit], builder: &mut CnfBuilder) -> Lit {
    assert_eq!(lhs.len(), rhs.len(), "bitvector width mismatch");
    let mut eq_bits = Vec::with_capacity(lhs.len());
    for (lhs, rhs) in lhs.iter().zip(rhs.iter()) {
        eq_bits.push(builder.eq(*lhs, *rhs));
    }
    builder.and_all(eq_bits)
}

fn bv_ite(cond: Lit, then_bits: &[Lit], else_bits: &[Lit], builder: &mut CnfBuilder) -> Vec<Lit> {
    assert_eq!(then_bits.len(), else_bits.len(), "bitvector width mismatch");
    then_bits
        .iter()
        .zip(else_bits.iter())
        .map(|(then_bit, else_bit)| builder.ite(cond, *then_bit, *else_bit))
        .collect()
}

fn bv_add(lhs: &[Lit], rhs: &[Lit], builder: &mut CnfBuilder) -> Vec<Lit> {
    assert_eq!(lhs.len(), rhs.len(), "bitvector width mismatch");
    let mut carry = builder.const_false();
    let mut out = Vec::with_capacity(lhs.len());
    for (lhs_bit, rhs_bit) in lhs.iter().zip(rhs.iter()) {
        let sum = builder.xor3(*lhs_bit, *rhs_bit, carry);
        carry = builder.majority3(*lhs_bit, *rhs_bit, carry);
        out.push(sum);
    }
    out
}

fn bv_neg(bits: &[Lit], builder: &mut CnfBuilder) -> Vec<Lit> {
    let inverted = bits.iter().map(|bit| builder.not(*bit)).collect::<Vec<_>>();
    let one = one_constant(bits.len() as u32, builder);
    bv_add(&inverted, &one, builder)
}

fn bv_sub(lhs: &[Lit], rhs: &[Lit], builder: &mut CnfBuilder) -> Vec<Lit> {
    let neg_rhs = bv_neg(rhs, builder);
    bv_add(lhs, &neg_rhs, builder)
}

fn bv_mul(lhs: &[Lit], rhs: &[Lit], builder: &mut CnfBuilder) -> Vec<Lit> {
    assert_eq!(lhs.len(), rhs.len(), "bitvector width mismatch");
    let width = lhs.len();
    let mut acc = vec![builder.const_false(); width];
    for (shift, rhs_bit) in rhs.iter().enumerate() {
        let mut partial = vec![builder.const_false(); width];
        for index in shift..width {
            partial[index] = builder.and(lhs[index - shift], *rhs_bit);
        }
        acc = bv_add(&acc, &partial, builder);
    }
    acc
}

fn bv_lt(lhs: &[Lit], rhs: &[Lit], signed: bool, builder: &mut CnfBuilder) -> Lit {
    assert_eq!(lhs.len(), rhs.len(), "bitvector width mismatch");
    if signed {
        let lhs_sign = lhs[lhs.len() - 1];
        let rhs_sign = rhs[rhs.len() - 1];
        let signs_differ = builder.xor(lhs_sign, rhs_sign);
        let unsigned_lt = bv_lt(lhs, rhs, false, builder);
        return builder.ite(signs_differ, lhs_sign, unsigned_lt);
    }

    let mut prefix_eq = builder.const_true();
    let mut less = builder.const_false();
    for index in (0..lhs.len()).rev() {
        let lhs_zero_rhs_one = builder.and(builder.not(lhs[index]), rhs[index]);
        let at_index = builder.and(prefix_eq, lhs_zero_rhs_one);
        less = builder.or(less, at_index);
        let eq = builder.eq(lhs[index], rhs[index]);
        prefix_eq = builder.and(prefix_eq, eq);
    }
    less
}

fn bv_shift_left(value: &[Lit], amount: &[Lit], builder: &mut CnfBuilder) -> Vec<Lit> {
    let fill = builder.const_false();
    bv_shift(value, amount, ShiftKind::Left, fill, builder)
}

fn bv_shift_right(
    value: &[Lit],
    amount: &[Lit],
    signed: bool,
    builder: &mut CnfBuilder,
) -> Vec<Lit> {
    let fill = if signed {
        value[value.len() - 1]
    } else {
        builder.const_false()
    };
    bv_shift(value, amount, ShiftKind::Right, fill, builder)
}

#[derive(Clone, Copy)]
enum ShiftKind {
    Left,
    Right,
}

fn bv_shift(
    value: &[Lit],
    amount: &[Lit],
    kind: ShiftKind,
    fill: Lit,
    builder: &mut CnfBuilder,
) -> Vec<Lit> {
    let width = value.len();
    let mut result = value.to_vec();
    let useful_bits = bit_width_for(width.max(1) as u64 - 1) as usize;

    for bit_index in 0..useful_bits.min(amount.len()) {
        let shift = 1usize << bit_index;
        let shifted = match kind {
            ShiftKind::Left => shift_left_const(&result, shift, fill),
            ShiftKind::Right => shift_right_const(&result, shift, fill),
        };
        result = guarded_bits(amount[bit_index], &shifted, &result, builder);
    }

    let overflow = builder.or_all(amount.iter().skip(useful_bits).copied());
    let overflow_value = vec![fill; width];
    guarded_bits(overflow, &overflow_value, &result, builder)
}

fn shift_left_const(value: &[Lit], amount: usize, fill: Lit) -> Vec<Lit> {
    (0..value.len())
        .map(|index| {
            if index >= amount {
                value[index - amount]
            } else {
                fill
            }
        })
        .collect()
}

fn shift_right_const(value: &[Lit], amount: usize, fill: Lit) -> Vec<Lit> {
    (0..value.len())
        .map(|index| {
            let source = index + amount;
            if source < value.len() {
                value[source]
            } else {
                fill
            }
        })
        .collect()
}

fn cast_bits(
    value: &[Lit],
    source: ExprType,
    target: ScalarType,
    builder: &CnfBuilder,
) -> Vec<Lit> {
    match source {
        ExprType::Bool => {
            if target.width == 1 {
                vec![value[0]]
            } else {
                let mut out = vec![value[0]];
                out.extend(
                    std::iter::repeat(builder.const_false()).take(target.width as usize - 1),
                );
                out
            }
        }
        ExprType::Scalar(source) => {
            if source.width == target.width {
                value.to_vec()
            } else if source.width < target.width {
                let fill = if source.signed {
                    value[value.len() - 1]
                } else {
                    builder.const_false()
                };
                let mut out = value.to_vec();
                out.extend(std::iter::repeat(fill).take((target.width - source.width) as usize));
                out
            } else {
                value[..target.width as usize].to_vec()
            }
        }
    }
}

fn one_constant(width: u32, builder: &CnfBuilder) -> Vec<Lit> {
    let mut bits = vec![builder.const_false(); width as usize];
    if let Some(first) = bits.first_mut() {
        *first = builder.const_true();
    }
    bits
}

fn bit_width_for(max_value: u64) -> u32 {
    let width = 64 - max_value.leading_zeros();
    width.max(1)
}
