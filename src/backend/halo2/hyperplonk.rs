#![cfg(feature = "backend-hyperplonk")]

use plonkish_backend::{
    backend::{
        hyperplonk::{HyperPlonk, HyperPlonkVerifierParam},
        PlonkishBackend, PlonkishCircuit, PlonkishCircuitInfo,
    },
    halo2_curves::bn256::{Bn256, Fr},
    pcs::{multilinear::Zeromorph, univariate::UnivariateKzg},
    util::{
        arithmetic::Field,
        expression::{Expression, Query, Rotation},
        transcript::{InMemoryTranscript, Keccak256Transcript},
    },
    Error as PlonkishError,
};
use rand08::{rngs::StdRng, SeedableRng};

use crate::backend::{
    cnf::Lit,
    phase2::{
        FormulaCommitment, UnsatPublicStatement, ValidatedResolutionInstance, ValidatedSatInstance,
    },
};

type Pcs = Zeromorph<UnivariateKzg<Bn256>>;
type ProofSystem = HyperPlonk<Pcs>;
type VerifierParam = HyperPlonkVerifierParam<Fr, Pcs>;

#[derive(Debug, Clone)]
pub struct HyperPlonkSatProof {
    pub commitment: FormulaCommitment,
    pub verifier_param: VerifierParam,
    pub proof: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct HyperPlonkResolutionProof {
    pub circuit_k: usize,
    pub verifier_param: VerifierParam,
    pub proof: Vec<u8>,
}

#[derive(Debug, thiserror::Error)]
pub enum HyperPlonkBackendError {
    #[error("hyperplonk proof commitment does not match the validated formula commitment")]
    CommitmentMismatch,
    #[error("hyperplonk received an invalid resolution instance: {0}")]
    InvalidResolutionInstance(String),
    #[error("hyperplonk backend failed: {0:?}")]
    Backend(PlonkishError),
}

#[derive(Clone, Debug)]
struct SatCircuit {
    info: PlonkishCircuitInfo<Fr>,
    instances: Vec<Vec<Fr>>,
    witness: Vec<Vec<Fr>>,
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SatDesign {
    SplitAssignment,
    CompactValue,
}

const DEFAULT_SAT_DESIGN: SatDesign = SatDesign::CompactValue;

#[derive(Clone, Debug)]
struct ResolutionCircuit {
    info: PlonkishCircuitInfo<Fr>,
    instances: Vec<Vec<Fr>>,
    witness: Vec<Vec<Fr>>,
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ResolutionDesign {
    WideLookup,
    EncodedLookup,
}

const DEFAULT_RESOLUTION_DESIGN: ResolutionDesign = ResolutionDesign::EncodedLookup;

impl From<PlonkishError> for HyperPlonkBackendError {
    fn from(value: PlonkishError) -> Self {
        Self::Backend(value)
    }
}

impl SatCircuit {
    fn new(instance: &ValidatedSatInstance) -> Self {
        Self::new_with_design(instance, DEFAULT_SAT_DESIGN)
    }

    fn new_with_design(instance: &ValidatedSatInstance, design: SatDesign) -> Self {
        match design {
            SatDesign::SplitAssignment => Self::new_split_assignment(instance),
            SatDesign::CompactValue => Self::new_compact_value(instance),
        }
    }

    fn new_split_assignment(instance: &ValidatedSatInstance) -> Self {
        let width = instance.commitment.max_clause_width.max(1) as usize;
        let support_vars = sat_support_vars(instance);
        let active_rows = 1 + support_vars.len() + instance.formula.clauses.len();
        let (k, size) = circuit_shape(active_rows);

        let mut q_var = vec![Fr::ZERO; size];
        let mut q_clause = vec![Fr::ZERO; size];
        let mut var_id_table = vec![Fr::ZERO; size];

        let mut m0 = vec![Fr::ZERO; size];
        let mut m1 = vec![Fr::ZERO; size];
        let mut pos_vars = vec![vec![Fr::ZERO; size]; width];
        let mut neg_vars = vec![vec![Fr::ZERO; size]; width];
        let mut pos_truths = vec![vec![Fr::ZERO; size]; width];
        let mut neg_truths = vec![vec![Fr::ZERO; size]; width];

        for (row_offset, var_id) in support_vars.iter().copied().enumerate() {
            let row = 1 + row_offset;
            let assigned = instance.assignment[var_id as usize - 1];
            q_var[row] = Fr::ONE;
            var_id_table[row] = field_u64(var_id as u64);
            m1[row] = field_bool(assigned);
            m0[row] = field_bool(!assigned);
        }

        let clause_row_start = 1 + support_vars.len();
        for (clause_idx, clause) in instance.formula.clauses.iter().enumerate() {
            let row = clause_row_start + clause_idx;
            q_clause[row] = Fr::ONE;

            for (slot, &lit) in clause.iter().enumerate() {
                let truth = field_bool(instance.clause_truth_rows[clause_idx][slot]);
                if lit > 0 {
                    pos_vars[slot][row] = field_u64(lit as u64);
                    pos_truths[slot][row] = truth;
                } else {
                    neg_vars[slot][row] = field_u64((-lit) as u64);
                    neg_truths[slot][row] = truth;
                }
            }
        }

        let preprocess_polys = vec![q_var, q_clause, var_id_table];
        let mut witness = vec![m0, m1];
        witness.extend(pos_vars);
        witness.extend(neg_vars);
        witness.extend(pos_truths);
        witness.extend(neg_truths);

        let q_var_expr = poly(0);
        let q_clause_expr = poly(1);
        let var_id_expr = poly(2);

        let witness_offset = preprocess_polys.len();
        let m0_expr = poly(witness_offset);
        let m1_expr = poly(witness_offset + 1);
        let pos_base = witness_offset + 2;
        let neg_base = pos_base + width;
        let pos_truth_base = neg_base + width;
        let neg_truth_base = pos_truth_base + width;

        let one = Expression::one();
        let mut constraints = vec![
            q_var_expr.clone() * boolean_expr(m0_expr.clone()),
            q_var_expr.clone() * boolean_expr(m1_expr.clone()),
            q_var_expr.clone() * (m0_expr.clone() + m1_expr.clone() - one.clone()),
        ];

        let mut all_false = one.clone();
        let mut lookups = Vec::new();

        for slot in 0..width {
            let pos_expr = poly(pos_base + slot);
            let neg_expr = poly(neg_base + slot);
            let pos_truth_expr = poly(pos_truth_base + slot);
            let neg_truth_expr = poly(neg_truth_base + slot);
            let slot_truth_expr = pos_truth_expr.clone() + neg_truth_expr.clone();

            constraints.push(q_clause_expr.clone() * pos_expr.clone() * neg_expr.clone());
            all_false = all_false * (one.clone() - slot_truth_expr);

            lookups.push(vec![
                (q_clause_expr.clone() * pos_expr, var_id_expr.clone()),
                (q_clause_expr.clone() * pos_truth_expr, m1_expr.clone()),
            ]);
            lookups.push(vec![
                (q_clause_expr.clone() * neg_expr, var_id_expr.clone()),
                (q_clause_expr.clone() * neg_truth_expr, m0_expr.clone()),
            ]);
        }

        constraints.push(q_clause_expr * all_false);

        let info = PlonkishCircuitInfo {
            k,
            num_instances: vec![],
            preprocess_polys,
            num_witness_polys: vec![witness.len()],
            num_challenges: vec![0],
            constraints,
            lookups,
            permutations: Vec::new(),
            max_degree: Some(width + 2),
        };

        Self {
            info,
            instances: Vec::new(),
            witness,
        }
    }

    fn new_compact_value(instance: &ValidatedSatInstance) -> Self {
        let width = instance.commitment.max_clause_width.max(1) as usize;
        let support_vars = sat_support_vars(instance);
        let active_rows = 1 + support_vars.len() + instance.formula.clauses.len();
        let (k, size) = circuit_shape(active_rows);

        let mut q_var = vec![Fr::ZERO; size];
        let mut q_clause = vec![Fr::ZERO; size];
        let mut var_id_table = vec![Fr::ZERO; size];

        let mut value = vec![Fr::ZERO; size];
        let mut pos_vars = vec![vec![Fr::ZERO; size]; width];
        let mut neg_vars = vec![vec![Fr::ZERO; size]; width];
        let mut pos_truths = vec![vec![Fr::ZERO; size]; width];
        let mut neg_truths = vec![vec![Fr::ZERO; size]; width];

        for (row_offset, var_id) in support_vars.iter().copied().enumerate() {
            let row = 1 + row_offset;
            let assigned = instance.assignment[var_id as usize - 1];
            q_var[row] = Fr::ONE;
            var_id_table[row] = field_u64(var_id as u64);
            value[row] = field_bool(assigned);
        }

        let clause_row_start = 1 + support_vars.len();
        for (clause_idx, clause) in instance.formula.clauses.iter().enumerate() {
            let row = clause_row_start + clause_idx;
            q_clause[row] = Fr::ONE;

            for (slot, &lit) in clause.iter().enumerate() {
                let truth = field_bool(instance.clause_truth_rows[clause_idx][slot]);
                if lit > 0 {
                    pos_vars[slot][row] = field_u64(lit as u64);
                    pos_truths[slot][row] = truth;
                } else {
                    neg_vars[slot][row] = field_u64((-lit) as u64);
                    neg_truths[slot][row] = truth;
                }
            }
        }

        let preprocess_polys = vec![q_var, q_clause, var_id_table];
        let mut witness = vec![value];
        witness.extend(pos_vars);
        witness.extend(neg_vars);
        witness.extend(pos_truths);
        witness.extend(neg_truths);

        let q_var_expr = poly(0);
        let q_clause_expr = poly(1);
        let var_id_expr = poly(2);

        let witness_offset = preprocess_polys.len();
        let value_expr = poly(witness_offset);
        let pos_base = witness_offset + 1;
        let neg_base = pos_base + width;
        let pos_truth_base = neg_base + width;
        let neg_truth_base = pos_truth_base + width;

        let one = Expression::one();
        let mut constraints = vec![q_var_expr.clone() * boolean_expr(value_expr.clone())];

        let mut all_false = one.clone();
        let mut lookups = Vec::new();

        for slot in 0..width {
            let pos_expr = poly(pos_base + slot);
            let neg_expr = poly(neg_base + slot);
            let pos_truth_expr = poly(pos_truth_base + slot);
            let neg_truth_expr = poly(neg_truth_base + slot);
            let slot_truth_expr = pos_truth_expr.clone() + neg_truth_expr.clone();

            constraints.push(q_clause_expr.clone() * pos_expr.clone() * neg_expr.clone());
            all_false = all_false * (one.clone() - slot_truth_expr);

            lookups.push(vec![
                (q_clause_expr.clone() * pos_expr, var_id_expr.clone()),
                (
                    q_clause_expr.clone() * pos_truth_expr,
                    q_var_expr.clone() * value_expr.clone(),
                ),
            ]);
            lookups.push(vec![
                (q_clause_expr.clone() * neg_expr, var_id_expr.clone()),
                (
                    q_clause_expr.clone() * neg_truth_expr,
                    q_var_expr.clone() * (one.clone() - value_expr.clone()),
                ),
            ]);
        }

        constraints.push(q_clause_expr * all_false);

        let info = PlonkishCircuitInfo {
            k,
            num_instances: vec![],
            preprocess_polys,
            num_witness_polys: vec![witness.len()],
            num_challenges: vec![0],
            constraints,
            lookups,
            permutations: Vec::new(),
            max_degree: Some(width + 2),
        };

        Self {
            info,
            instances: Vec::new(),
            witness,
        }
    }
}

impl ResolutionCircuit {
    fn new(instance: &ValidatedResolutionInstance) -> Result<Self, HyperPlonkBackendError> {
        Self::new_with_design(instance, DEFAULT_RESOLUTION_DESIGN)
    }

    fn new_with_design(
        instance: &ValidatedResolutionInstance,
        design: ResolutionDesign,
    ) -> Result<Self, HyperPlonkBackendError> {
        let statement = instance.public_statement();
        let width = statement.max_clause_width.max(1) as usize;
        let formula_clause_count = instance.formula.clauses.len();
        let step_count = instance
            .proof
            .steps
            .len()
            .max(instance.expanded_steps.len());
        let table_clause_count = (formula_clause_count + step_count).max(1);
        let step_row_start = 1 + table_clause_count;
        let active_rows = step_row_start + step_count;
        let (k, size) = circuit_shape(active_rows);
        let instances = resolution_public_inputs(&statement, size);

        let meta_num_vars = vec![field_u64(statement.num_vars as u64); size];
        let meta_num_clauses = vec![field_u64(statement.num_clauses as u64); size];
        let meta_max_width = vec![field_u64(statement.max_clause_width as u64); size];

        let mut q_table = vec![Fr::ZERO; size];
        let mut q_step = vec![Fr::ZERO; size];
        let mut q_final = vec![Fr::ZERO; size];
        let mut clause_table_id = vec![Fr::ZERO; size];
        let mut clause_table_lits = vec![vec![Fr::ZERO; size]; width];
        let mut positive_value_table = vec![Fr::ZERO; size];
        let mut variable_positive_table = vec![Fr::ZERO; size];
        let mut variable_value_table = vec![Fr::ZERO; size];

        let mut left_id = vec![Fr::ZERO; size];
        let mut right_id = vec![Fr::ZERO; size];
        let mut derived_id = vec![Fr::ZERO; size];
        let mut left_gap = vec![Fr::ZERO; size];
        let mut right_gap = vec![Fr::ZERO; size];
        let mut pivot = vec![Fr::ZERO; size];
        let mut left_lits = vec![vec![Fr::ZERO; size]; width];
        let mut right_lits = vec![vec![Fr::ZERO; size]; width];
        let mut shuffled_left = vec![vec![Fr::ZERO; size]; width];
        let mut shuffled_right = vec![vec![Fr::ZERO; size]; width];
        let mut derived_lits = vec![vec![Fr::ZERO; size]; width];
        let mut left_abs = vec![vec![Fr::ZERO; size]; width];
        let mut left_sign = vec![vec![Fr::ZERO; size]; width];
        let mut right_abs = vec![vec![Fr::ZERO; size]; width];
        let mut right_sign = vec![vec![Fr::ZERO; size]; width];
        let mut derived_abs = vec![vec![Fr::ZERO; size]; width];
        let mut derived_sign = vec![vec![Fr::ZERO; size]; width];

        let mut permutations = Vec::new();
        let instance_count = instances.len();
        let preprocess_offset = instance_count;
        let preprocess_count = 10 + width;
        let witness_offset = instance_count + preprocess_count;
        let left_base = witness_offset + 6;
        let right_base = left_base + width;
        let shuffled_left_base = right_base + width;
        let shuffled_right_base = shuffled_left_base + width;
        let derived_base = shuffled_right_base + width;
        let left_abs_base = derived_base + width;
        let left_sign_base = left_abs_base + width;
        let right_abs_base = left_sign_base + width;
        let right_sign_base = right_abs_base + width;
        let derived_abs_base = right_sign_base + width;
        let derived_sign_base = derived_abs_base + width;

        for (row, value) in positive_value_table.iter_mut().enumerate() {
            *value = field_u64((row + 1) as u64);
        }

        let num_vars = statement.num_vars as usize;
        let positive_var_rows = num_vars.max(1);
        for row in 0..size {
            if row < positive_var_rows {
                variable_positive_table[row] = field_u64((row + 1) as u64);
            } else {
                variable_positive_table[row] = field_u64(1);
            }
        }
        for row in 0..size {
            if row <= num_vars {
                variable_value_table[row] = field_u64(row as u64);
            } else {
                variable_value_table[row] = Fr::ZERO;
            }
        }

        for (clause_idx, clause) in instance.formula.clauses.iter().enumerate() {
            let row = 1 + clause_idx;
            q_table[row] = Fr::ONE;
            clause_table_id[row] = field_u64((clause_idx + 1) as u64);
            for (slot, lit) in clause.iter().take(width).copied().enumerate() {
                clause_table_lits[slot][row] = encode_lit(lit);
            }
        }

        for step_idx in 0..step_count {
            let table_row = 1 + formula_clause_count + step_idx;
            let row = step_row_start + step_idx;
            let proof_step = instance.proof.steps.get(step_idx);
            let expanded_step = instance.expanded_steps.get(step_idx);
            q_table[table_row] = Fr::ONE;
            q_step[row] = Fr::ONE;
            if step_idx + 1 == step_count {
                q_final[row] = Fr::ONE;
            }

            let left_parent = proof_step.map(|step| step.left_parent).unwrap_or(0);
            let right_parent = proof_step.map(|step| step.right_parent).unwrap_or(0);
            let pivot_var = proof_step
                .map(|step| step.pivot_var)
                .or_else(|| expanded_step.map(|step| step.pivot_var))
                .unwrap_or(0);

            left_id[row] = field_u64(left_parent as u64);
            right_id[row] = field_u64(right_parent as u64);
            derived_id[row] = field_u64((instance.formula.clauses.len() + step_idx + 1) as u64);
            let derived_index = instance.formula.clauses.len() + step_idx + 1;
            let left_gap_value = derived_index.saturating_sub(left_parent as usize) as u64;
            let right_gap_value = derived_index.saturating_sub(right_parent as usize) as u64;
            left_gap[row] = field_u64(left_gap_value);
            right_gap[row] = field_u64(right_gap_value);
            pivot[row] = field_u64(pivot_var as u64);
            clause_table_id[table_row] = field_u64(derived_index as u64);

            for (slot, lit) in expanded_step
                .map(|step| step.left_clause.as_slice())
                .unwrap_or(&[])
                .iter()
                .take(width)
                .copied()
                .enumerate()
            {
                left_lits[slot][row] = encode_lit(lit);
                left_abs[slot][row] = literal_abs(lit);
                left_sign[slot][row] = literal_sign(lit);
            }
            for (slot, lit) in expanded_step
                .map(|step| step.right_clause.as_slice())
                .unwrap_or(&[])
                .iter()
                .take(width)
                .copied()
                .enumerate()
            {
                right_lits[slot][row] = encode_lit(lit);
                right_abs[slot][row] = literal_abs(lit);
                right_sign[slot][row] = literal_sign(lit);
            }
            for (slot, lit) in expanded_step
                .map(|step| step.resolvent.as_slice())
                .unwrap_or(&[])
                .iter()
                .take(width)
                .copied()
                .enumerate()
            {
                derived_lits[slot][row] = encode_lit(lit);
                derived_abs[slot][row] = literal_abs(lit);
                derived_sign[slot][row] = literal_sign(lit);
                clause_table_lits[slot][table_row] = encode_lit(lit);
            }

            let (left_perm, arranged_left) = arrange_clause_with_pivot(
                expanded_step
                    .map(|step| step.left_clause.as_slice())
                    .unwrap_or(&[]),
                pivot_var as Lit,
                width,
            );
            let (right_perm, arranged_right) = arrange_clause_with_pivot(
                expanded_step
                    .map(|step| step.right_clause.as_slice())
                    .unwrap_or(&[]),
                -(pivot_var as Lit),
                width,
            );

            for slot in 0..width {
                shuffled_left[slot][row] = arranged_left[slot];
                shuffled_right[slot][row] = arranged_right[slot];

                let left_target = left_perm[slot];
                let right_target = right_perm[slot];
                permutations.push(vec![
                    (left_base + slot, row),
                    (shuffled_left_base + left_target, row),
                ]);
                permutations.push(vec![
                    (right_base + slot, row),
                    (shuffled_right_base + right_target, row),
                ]);
            }
        }

        let preprocess_polys = {
            let mut polys = vec![
                meta_num_vars,
                meta_num_clauses,
                meta_max_width,
                q_table,
                q_step,
                q_final,
                clause_table_id,
            ];
            polys.extend(clause_table_lits);
            polys.push(positive_value_table);
            polys.push(variable_positive_table);
            polys.push(variable_value_table);
            polys
        };

        let mut witness = vec![left_id, right_id, derived_id, left_gap, right_gap, pivot];
        witness.extend(left_lits);
        witness.extend(right_lits);
        witness.extend(shuffled_left);
        witness.extend(shuffled_right);
        witness.extend(derived_lits);
        witness.extend(left_abs);
        witness.extend(left_sign);
        witness.extend(right_abs);
        witness.extend(right_sign);
        witness.extend(derived_abs);
        witness.extend(derived_sign);

        let public_num_vars_expr = poly(0);
        let public_num_clauses_expr = poly(1);
        let public_max_width_expr = poly(2);
        let meta_num_vars_expr = poly(preprocess_offset);
        let meta_num_clauses_expr = poly(preprocess_offset + 1);
        let meta_max_width_expr = poly(preprocess_offset + 2);
        let q_table_expr = poly(preprocess_offset + 3);
        let q_step_expr = poly(preprocess_offset + 4);
        let q_final_expr = poly(preprocess_offset + 5);
        let mut preprocess_cursor = preprocess_offset + 6;
        let clause_table_id_expr = poly(preprocess_cursor);
        preprocess_cursor += 1;
        let clause_table_lit_exprs = (0..width)
            .map(|slot| poly(preprocess_cursor + slot))
            .collect::<Vec<_>>();
        preprocess_cursor += width;
        let positive_value_expr = poly(preprocess_cursor);
        preprocess_cursor += 1;
        let variable_positive_expr = poly(preprocess_cursor);
        preprocess_cursor += 1;
        let variable_value_expr = poly(preprocess_cursor);

        let left_id_expr = poly(witness_offset);
        let right_id_expr = poly(witness_offset + 1);
        let derived_id_expr = poly(witness_offset + 2);
        let left_gap_expr = poly(witness_offset + 3);
        let right_gap_expr = poly(witness_offset + 4);
        let pivot_expr = poly(witness_offset + 5);
        let left_exprs = (0..width)
            .map(|slot| poly(left_base + slot))
            .collect::<Vec<_>>();
        let right_exprs = (0..width)
            .map(|slot| poly(right_base + slot))
            .collect::<Vec<_>>();
        let shuffled_left_exprs = (0..width)
            .map(|slot| poly(shuffled_left_base + slot))
            .collect::<Vec<_>>();
        let shuffled_right_exprs = (0..width)
            .map(|slot| poly(shuffled_right_base + slot))
            .collect::<Vec<_>>();
        let derived_exprs = (0..width)
            .map(|slot| poly(derived_base + slot))
            .collect::<Vec<_>>();
        let left_abs_exprs = (0..width)
            .map(|slot| poly(left_abs_base + slot))
            .collect::<Vec<_>>();
        let left_sign_exprs = (0..width)
            .map(|slot| poly(left_sign_base + slot))
            .collect::<Vec<_>>();
        let right_abs_exprs = (0..width)
            .map(|slot| poly(right_abs_base + slot))
            .collect::<Vec<_>>();
        let right_sign_exprs = (0..width)
            .map(|slot| poly(right_sign_base + slot))
            .collect::<Vec<_>>();
        let derived_abs_exprs = (0..width)
            .map(|slot| poly(derived_abs_base + slot))
            .collect::<Vec<_>>();
        let derived_sign_exprs = (0..width)
            .map(|slot| poly(derived_sign_base + slot))
            .collect::<Vec<_>>();
        let selected_clause_table_id_expr = q_table_expr.clone() * clause_table_id_expr.clone();
        let selected_clause_table_lit_exprs = clause_table_lit_exprs
            .iter()
            .cloned()
            .map(|expr| q_table_expr.clone() * expr)
            .collect::<Vec<_>>();

        let mut constraints = vec![
            meta_num_vars_expr - public_num_vars_expr,
            meta_num_clauses_expr - public_num_clauses_expr,
            meta_max_width_expr - public_max_width_expr,
        ];
        constraints.push(
            q_step_expr.clone()
                * (left_gap_expr.clone() + left_id_expr.clone() - derived_id_expr.clone()),
        );
        constraints.push(
            q_step_expr.clone()
                * (right_gap_expr.clone() + right_id_expr.clone() - derived_id_expr.clone()),
        );
        constraints
            .push(q_step_expr.clone() * (shuffled_left_exprs[0].clone() - pivot_expr.clone()));
        constraints
            .push(q_step_expr.clone() * (shuffled_right_exprs[0].clone() + pivot_expr.clone()));

        for derived in &derived_exprs {
            constraints.push(q_final_expr.clone() * derived.clone());
        }

        for (lit, (abs, sign)) in left_exprs
            .iter()
            .zip(left_abs_exprs.iter().zip(left_sign_exprs.iter()))
        {
            constraints.push(q_step_expr.clone() * boolean_expr(sign.clone()));
            constraints.push(
                q_step_expr.clone()
                    * (lit.clone() - signed_literal_expr(abs.clone(), sign.clone())),
            );
        }
        for (lit, (abs, sign)) in right_exprs
            .iter()
            .zip(right_abs_exprs.iter().zip(right_sign_exprs.iter()))
        {
            constraints.push(q_step_expr.clone() * boolean_expr(sign.clone()));
            constraints.push(
                q_step_expr.clone()
                    * (lit.clone() - signed_literal_expr(abs.clone(), sign.clone())),
            );
        }
        for (lit, (abs, sign)) in derived_exprs
            .iter()
            .zip(derived_abs_exprs.iter().zip(derived_sign_exprs.iter()))
        {
            constraints.push(q_step_expr.clone() * boolean_expr(sign.clone()));
            constraints.push(
                q_step_expr.clone()
                    * (lit.clone() - signed_literal_expr(abs.clone(), sign.clone())),
            );
        }

        for lit in shuffled_left_exprs.iter().skip(1) {
            let mut membership = lit.clone();
            for derived in &derived_exprs {
                membership = membership * (lit.clone() - derived.clone());
            }
            constraints.push(q_step_expr.clone() * membership);
        }

        for lit in shuffled_right_exprs.iter().skip(1) {
            let mut membership = lit.clone();
            for derived in &derived_exprs {
                membership = membership * (lit.clone() - derived.clone());
            }
            constraints.push(q_step_expr.clone() * membership);
        }

        for derived in &derived_exprs {
            let mut membership = derived.clone();
            for lit in shuffled_left_exprs.iter().skip(1) {
                membership = membership * (derived.clone() - lit.clone());
            }
            for lit in shuffled_right_exprs.iter().skip(1) {
                membership = membership * (derived.clone() - lit.clone());
            }
            constraints.push(q_step_expr.clone() * membership);
        }

        let lookups = match design {
            ResolutionDesign::WideLookup => {
                let mut lookups = vec![
                    clause_lookup(
                        q_step_expr.clone(),
                        left_id_expr.clone(),
                        &left_exprs,
                        selected_clause_table_id_expr.clone(),
                        &selected_clause_table_lit_exprs,
                    ),
                    clause_lookup(
                        q_step_expr.clone(),
                        right_id_expr.clone(),
                        &right_exprs,
                        selected_clause_table_id_expr.clone(),
                        &selected_clause_table_lit_exprs,
                    ),
                    clause_lookup(
                        q_step_expr.clone(),
                        derived_id_expr.clone(),
                        &derived_exprs,
                        selected_clause_table_id_expr.clone(),
                        &selected_clause_table_lit_exprs,
                    ),
                ];
                lookups.push(vec![(
                    selected_lookup_expr(q_step_expr.clone(), pivot_expr.clone(), Fr::ONE),
                    variable_positive_expr.clone(),
                )]);
                lookups.push(vec![(
                    selected_lookup_expr(q_step_expr.clone(), left_id_expr.clone(), Fr::ONE),
                    positive_value_expr.clone(),
                )]);
                lookups.push(vec![(
                    selected_lookup_expr(q_step_expr.clone(), right_id_expr.clone(), Fr::ONE),
                    positive_value_expr.clone(),
                )]);
                lookups.push(vec![(
                    selected_lookup_expr(q_step_expr.clone(), left_gap_expr.clone(), Fr::ONE),
                    positive_value_expr.clone(),
                )]);
                lookups.push(vec![(
                    selected_lookup_expr(q_step_expr.clone(), right_gap_expr.clone(), Fr::ONE),
                    positive_value_expr.clone(),
                )]);
                for abs in left_abs_exprs
                    .iter()
                    .chain(right_abs_exprs.iter())
                    .chain(derived_abs_exprs.iter())
                {
                    lookups.push(vec![(
                        selected_lookup_expr(q_step_expr.clone(), abs.clone(), Fr::ZERO),
                        variable_value_expr.clone(),
                    )]);
                }
                lookups
            }
            ResolutionDesign::EncodedLookup => {
                let lookup_challenge = challenge(0);
                let selected_encoded_clause_expr = q_table_expr.clone()
                    * encoded_clause_expr(
                        clause_table_id_expr.clone(),
                        &clause_table_lit_exprs,
                        lookup_challenge.clone(),
                    );
                let mut lookups = vec![
                    vec![(
                        q_step_expr.clone()
                            * encoded_clause_expr(
                                left_id_expr.clone(),
                                &left_exprs,
                                lookup_challenge.clone(),
                            ),
                        selected_encoded_clause_expr.clone(),
                    )],
                    vec![(
                        q_step_expr.clone()
                            * encoded_clause_expr(
                                right_id_expr.clone(),
                                &right_exprs,
                                lookup_challenge.clone(),
                            ),
                        selected_encoded_clause_expr.clone(),
                    )],
                    vec![(
                        q_step_expr.clone()
                            * encoded_clause_expr(
                                derived_id_expr.clone(),
                                &derived_exprs,
                                lookup_challenge.clone(),
                            ),
                        selected_encoded_clause_expr,
                    )],
                ];
                lookups.push(vec![(
                    selected_lookup_expr(q_step_expr.clone(), pivot_expr, Fr::ONE),
                    variable_positive_expr.clone(),
                )]);
                lookups.push(vec![(
                    selected_lookup_expr(q_step_expr.clone(), left_id_expr, Fr::ONE),
                    positive_value_expr.clone(),
                )]);
                lookups.push(vec![(
                    selected_lookup_expr(q_step_expr.clone(), right_id_expr, Fr::ONE),
                    positive_value_expr.clone(),
                )]);
                lookups.push(vec![(
                    selected_lookup_expr(q_step_expr.clone(), left_gap_expr, Fr::ONE),
                    positive_value_expr.clone(),
                )]);
                lookups.push(vec![(
                    selected_lookup_expr(q_step_expr.clone(), right_gap_expr, Fr::ONE),
                    positive_value_expr.clone(),
                )]);
                for abs in left_abs_exprs
                    .iter()
                    .chain(right_abs_exprs.iter())
                    .chain(derived_abs_exprs.iter())
                {
                    lookups.push(vec![(
                        selected_lookup_expr(q_step_expr.clone(), abs.clone(), Fr::ZERO),
                        variable_value_expr.clone(),
                    )]);
                }
                lookups
            }
        };

        let info = PlonkishCircuitInfo {
            k,
            num_instances: instances.iter().map(Vec::len).collect(),
            preprocess_polys,
            num_witness_polys: vec![witness.len()],
            num_challenges: vec![match design {
                ResolutionDesign::WideLookup => 0,
                ResolutionDesign::EncodedLookup => 1,
            }],
            constraints,
            lookups,
            permutations,
            max_degree: Some((4 * width).max(8) + 4),
        };

        Ok(Self {
            info,
            instances,
            witness,
        })
    }
}

impl PlonkishCircuit<Fr> for SatCircuit {
    fn circuit_info_without_preprocess(&self) -> Result<PlonkishCircuitInfo<Fr>, PlonkishError> {
        Ok(self.info.clone())
    }

    fn circuit_info(&self) -> Result<PlonkishCircuitInfo<Fr>, PlonkishError> {
        Ok(self.info.clone())
    }

    fn instances(&self) -> &[Vec<Fr>] {
        &self.instances
    }

    fn synthesize(&self, round: usize, challenges: &[Fr]) -> Result<Vec<Vec<Fr>>, PlonkishError> {
        if round != 0 || !challenges.is_empty() {
            return Err(PlonkishError::InvalidInput(
                "sat circuit only supports a single witness round without challenges".to_owned(),
            ));
        }
        Ok(self.witness.clone())
    }
}

impl PlonkishCircuit<Fr> for ResolutionCircuit {
    fn circuit_info_without_preprocess(&self) -> Result<PlonkishCircuitInfo<Fr>, PlonkishError> {
        Ok(self.info.clone())
    }

    fn circuit_info(&self) -> Result<PlonkishCircuitInfo<Fr>, PlonkishError> {
        Ok(self.info.clone())
    }

    fn instances(&self) -> &[Vec<Fr>] {
        &self.instances
    }

    fn synthesize(&self, round: usize, challenges: &[Fr]) -> Result<Vec<Vec<Fr>>, PlonkishError> {
        if round != 0 || !challenges.is_empty() {
            return Err(PlonkishError::InvalidInput(
                "resolution circuit only supports a single witness round without challenges"
                    .to_owned(),
            ));
        }
        Ok(self.witness.clone())
    }
}

pub fn prove_sat(
    instance: &ValidatedSatInstance,
) -> Result<HyperPlonkSatProof, HyperPlonkBackendError> {
    let circuit = SatCircuit::new(instance);
    let circuit_info = circuit.circuit_info()?;
    let param = ProofSystem::setup(&circuit_info, seeded_rng())?;
    let (prover_param, verifier_param) = ProofSystem::preprocess(&param, &circuit_info)?;

    let proof = {
        let mut transcript = Keccak256Transcript::new(());
        ProofSystem::prove_with_shift(&prover_param, &circuit, &mut transcript, seeded_rng())?;
        transcript.into_proof()
    };

    let result = HyperPlonkSatProof {
        commitment: instance.commitment.clone(),
        verifier_param,
        proof,
    };
    verify_sat(instance, &result)?;
    Ok(result)
}

pub fn verify_sat(
    instance: &ValidatedSatInstance,
    proof: &HyperPlonkSatProof,
) -> Result<(), HyperPlonkBackendError> {
    if proof.commitment != instance.commitment {
        return Err(HyperPlonkBackendError::CommitmentMismatch);
    }

    let circuit = SatCircuit::new(instance);
    let mut transcript = Keccak256Transcript::from_proof((), proof.proof.as_slice());
    ProofSystem::verify_with_shift(
        &proof.verifier_param,
        circuit.instances(),
        &mut transcript,
        seeded_rng(),
    )?;
    Ok(())
}

pub fn prove_unsat(
    instance: &ValidatedResolutionInstance,
) -> Result<HyperPlonkResolutionProof, HyperPlonkBackendError> {
    let statement = instance.public_statement();
    let circuit = ResolutionCircuit::new(instance)?;
    let circuit_info = circuit.circuit_info()?;
    let param = ProofSystem::setup(&circuit_info, seeded_rng())?;
    let (prover_param, verifier_param) = ProofSystem::preprocess(&param, &circuit_info)?;

    let proof = {
        let mut transcript = Keccak256Transcript::new(());
        ProofSystem::prove_with_shift(&prover_param, &circuit, &mut transcript, seeded_rng())?;
        transcript.into_proof()
    };

    let result = HyperPlonkResolutionProof {
        circuit_k: circuit_info.k,
        verifier_param,
        proof,
    };
    verify_unsat(&statement, &result)?;
    Ok(result)
}

pub fn verify_unsat(
    statement: &UnsatPublicStatement,
    proof: &HyperPlonkResolutionProof,
) -> Result<(), HyperPlonkBackendError> {
    let size = 1usize << proof.circuit_k;
    let instances = resolution_public_inputs(statement, size);
    let mut transcript = Keccak256Transcript::from_proof((), proof.proof.as_slice());
    ProofSystem::verify_with_shift(
        &proof.verifier_param,
        &instances,
        &mut transcript,
        seeded_rng(),
    )?;
    Ok(())
}

fn resolution_public_inputs(statement: &UnsatPublicStatement, size: usize) -> Vec<Vec<Fr>> {
    vec![
        vec![field_u64(statement.num_vars as u64); size],
        vec![field_u64(statement.num_clauses as u64); size],
        vec![field_u64(statement.max_clause_width as u64); size],
    ]
}

fn sat_support_vars(instance: &ValidatedSatInstance) -> Vec<u32> {
    instance
        .formula
        .clauses
        .iter()
        .flat_map(|clause| clause.iter().map(|lit| lit.unsigned_abs()))
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn clause_lookup(
    selector: Expression<Fr>,
    id_expr: Expression<Fr>,
    clause_exprs: &[Expression<Fr>],
    table_id_expr: Expression<Fr>,
    table_clause_exprs: &[Expression<Fr>],
) -> Vec<(Expression<Fr>, Expression<Fr>)> {
    let mut lookup = vec![(selector.clone() * id_expr, table_id_expr)];
    lookup.extend(
        clause_exprs
            .iter()
            .cloned()
            .zip(table_clause_exprs.iter().cloned())
            .map(|(input, table)| (selector.clone() * input, table)),
    );
    lookup
}

fn arrange_clause_with_pivot(
    clause: &[Lit],
    requested_front_lit: Lit,
    width: usize,
) -> (Vec<usize>, Vec<Fr>) {
    let mut order = (0..clause.len().min(width)).collect::<Vec<_>>();
    if let Some(front_idx) = clause
        .iter()
        .position(|candidate| *candidate == requested_front_lit)
    {
        if front_idx < width {
            order.swap(0, front_idx);
        }
    }

    let mut permutation = vec![0usize; width];
    let mut arranged = vec![Fr::ZERO; width];

    for (new_idx, old_idx) in order.into_iter().enumerate() {
        arranged[new_idx] = encode_lit(clause[old_idx]);
        permutation[old_idx] = new_idx;
    }

    for idx in clause.len()..width {
        permutation[idx] = idx;
    }

    (permutation, arranged)
}

fn circuit_shape(active_rows: usize) -> (usize, usize) {
    let size = active_rows.max(2).next_power_of_two();
    (size.ilog2() as usize, size)
}

fn poly(index: usize) -> Expression<Fr> {
    Expression::Polynomial(Query::new(index, Rotation::cur()))
}

fn challenge(index: usize) -> Expression<Fr> {
    Expression::Challenge(index)
}

fn boolean_expr(expr: Expression<Fr>) -> Expression<Fr> {
    expr.clone() * (expr - Expression::one())
}

fn signed_literal_expr(abs_expr: Expression<Fr>, sign_expr: Expression<Fr>) -> Expression<Fr> {
    abs_expr * (Expression::one() - sign_expr * field_u64(2))
}

fn selected_lookup_expr(
    selector: Expression<Fr>,
    value: Expression<Fr>,
    inactive_value: Fr,
) -> Expression<Fr> {
    selector.clone() * value + (Expression::one() - selector) * inactive_value
}

fn encoded_clause_expr(
    id_expr: Expression<Fr>,
    clause_exprs: &[Expression<Fr>],
    randomizer: Expression<Fr>,
) -> Expression<Fr> {
    Expression::distribute_powers(
        std::iter::once(id_expr).chain(clause_exprs.iter().cloned()),
        randomizer,
    )
}

fn seeded_rng() -> StdRng {
    StdRng::seed_from_u64(7)
}

fn field_u64(value: u64) -> Fr {
    Fr::from(value)
}

fn field_bool(value: bool) -> Fr {
    if value {
        Fr::ONE
    } else {
        Fr::ZERO
    }
}

fn literal_abs(lit: Lit) -> Fr {
    field_u64(lit.unsigned_abs() as u64)
}

fn literal_sign(lit: Lit) -> Fr {
    field_bool(lit < 0)
}

fn encode_lit(lit: Lit) -> Fr {
    if lit == 0 {
        Fr::ZERO
    } else if lit > 0 {
        field_u64(lit as u64)
    } else {
        -field_u64((-lit) as u64)
    }
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, Instant};

    use rand08::{rngs::StdRng, Rng, SeedableRng};

    use crate::backend::{
        cnf::CnfFormula,
        phase2::{
            generate_resolution_proof_by_closure, validate_resolution_instance,
            validate_sat_instance, ResolutionProof, ResolutionStep, ValidatedResolutionInstance,
            ValidatedSatInstance,
        },
    };

    use super::*;

    #[test]
    fn proves_sat_with_lookup_table() {
        let formula = CnfFormula {
            num_vars: 2,
            clauses: vec![vec![1, -2], vec![2]],
        };
        let instance = validate_sat_instance(&formula, &[true, true]).unwrap();
        let proof = prove_sat(&instance).unwrap();
        verify_sat(&instance, &proof).unwrap();
    }

    #[test]
    fn sat_proof_depends_only_on_formula_existence_not_unused_assignment_bits() {
        let formula = CnfFormula {
            num_vars: 3,
            clauses: vec![vec![1]],
        };
        let left = validate_sat_instance(&formula, &[true, false, false]).unwrap();
        let right = validate_sat_instance(&formula, &[true, true, true]).unwrap();

        let left_circuit = SatCircuit::new(&left);
        let right_circuit = SatCircuit::new(&right);
        assert_eq!(left_circuit.info.k, right_circuit.info.k);
        assert_eq!(
            left_circuit.info.preprocess_polys,
            right_circuit.info.preprocess_polys
        );

        let proof = prove_sat(&left).unwrap();
        verify_sat(&right, &proof).unwrap();
    }

    #[test]
    fn proves_unsat_with_lookup_and_shuffle() {
        let formula = CnfFormula {
            num_vars: 1,
            clauses: vec![vec![1], vec![-1]],
        };
        let proof = generate_resolution_proof_by_closure(&formula, 8).unwrap();
        let instance = validate_resolution_instance(&formula, proof).unwrap();
        let proof = prove_unsat(&instance).unwrap();
        verify_unsat(&instance.public_statement(), &proof).unwrap();
    }

    #[test]
    fn proves_multi_step_unsat_with_lookup_and_shuffle() {
        let instance = synthetic_resolution_instance(2);
        let proof = prove_unsat(&instance).unwrap();
        verify_unsat(&instance.public_statement(), &proof).unwrap();
    }

    #[test]
    fn proves_width_four_unsat_with_lookup_and_shuffle() {
        let instance = synthetic_resolution_instance(4);
        let proof = prove_unsat(&instance).unwrap();
        verify_unsat(&instance.public_statement(), &proof).unwrap();
    }

    #[test]
    fn rejects_forged_unsat_instance_for_sat_formula() {
        let formula = CnfFormula {
            num_vars: 1,
            clauses: vec![vec![1]],
        };
        let instance = ValidatedResolutionInstance {
            commitment: FormulaCommitment::from_formula(&formula).unwrap(),
            formula,
            proof: ResolutionProof {
                steps: vec![ResolutionStep {
                    left_parent: 2,
                    right_parent: 2,
                    pivot_var: 0,
                    resolvent: vec![0],
                }],
            },
            expanded_steps: vec![crate::backend::phase2::ExpandedResolutionStep {
                pivot_var: 0,
                left_clause: vec![0],
                right_clause: vec![0],
                resolvent: vec![0],
            }],
        };

        let err = prove_unsat(&instance).unwrap_err();
        assert!(matches!(err, HyperPlonkBackendError::Backend(_)));
    }

    #[test]
    fn rejects_wrong_resolvent_even_when_shape_is_well_formed() {
        let formula = CnfFormula {
            num_vars: 2,
            clauses: vec![vec![1, 2], vec![-1]],
        };
        let instance = ValidatedResolutionInstance {
            commitment: FormulaCommitment::from_formula(&formula).unwrap(),
            formula,
            proof: ResolutionProof {
                steps: vec![ResolutionStep {
                    left_parent: 1,
                    right_parent: 2,
                    pivot_var: 1,
                    resolvent: vec![],
                }],
            },
            expanded_steps: vec![crate::backend::phase2::ExpandedResolutionStep {
                pivot_var: 1,
                left_clause: vec![1, 2],
                right_clause: vec![-1],
                resolvent: vec![],
            }],
        };

        let err = prove_unsat(&instance).unwrap_err();
        assert!(matches!(err, HyperPlonkBackendError::Backend(_)));
    }

    #[test]
    fn rejects_parent_clauses_not_present_in_formula_database() {
        let formula = CnfFormula {
            num_vars: 1,
            clauses: vec![vec![1], vec![-1]],
        };
        let instance = ValidatedResolutionInstance {
            commitment: FormulaCommitment::from_formula(&formula).unwrap(),
            formula,
            proof: ResolutionProof {
                steps: vec![ResolutionStep {
                    left_parent: 1,
                    right_parent: 2,
                    pivot_var: 1,
                    resolvent: vec![],
                }],
            },
            expanded_steps: vec![crate::backend::phase2::ExpandedResolutionStep {
                pivot_var: 1,
                left_clause: vec![2],
                right_clause: vec![-2],
                resolvent: vec![],
            }],
        };

        let err = prove_unsat(&instance).unwrap_err();
        assert!(matches!(err, HyperPlonkBackendError::Backend(_)));
    }

    #[test]
    fn rejects_out_of_range_literals_and_pivots() {
        let formula = CnfFormula {
            num_vars: 1,
            clauses: vec![vec![2], vec![-2]],
        };
        let instance = validate_resolution_instance(
            &formula,
            ResolutionProof {
                steps: vec![ResolutionStep {
                    left_parent: 1,
                    right_parent: 2,
                    pivot_var: 2,
                    resolvent: vec![],
                }],
            },
        )
        .unwrap();

        let err = prove_unsat(&instance).unwrap_err();
        assert!(matches!(err, HyperPlonkBackendError::Backend(_)));
    }

    #[derive(Debug, Clone)]
    struct SatBenchResult {
        avg_prove_ms: f64,
        avg_proof_bytes: usize,
        preprocess_cols: usize,
        witness_cols: usize,
        constraints: usize,
        lookups: usize,
    }

    #[derive(Debug, Clone)]
    struct ResolutionBenchResult {
        avg_prove_ms: f64,
        avg_proof_bytes: usize,
        preprocess_cols: usize,
        witness_cols: usize,
        constraints: usize,
        lookups: usize,
        challenges: usize,
    }

    fn synthetic_sat_instance(
        num_vars: usize,
        num_clauses: usize,
        width: usize,
        seed: u64,
    ) -> ValidatedSatInstance {
        let mut rng = StdRng::seed_from_u64(seed);
        let assignment = (0..num_vars).map(|_| rng.gen_bool(0.5)).collect::<Vec<_>>();
        let width = width.min(num_vars.max(1));
        let mut clauses = Vec::with_capacity(num_clauses);

        for _ in 0..num_clauses {
            let mut vars = Vec::with_capacity(width);
            while vars.len() < width {
                let candidate = rng.gen_range(1..=num_vars as i32);
                if !vars.contains(&candidate) {
                    vars.push(candidate);
                }
            }

            let mut clause = vars
                .iter()
                .map(|var| if rng.gen_bool(0.5) { *var } else { -*var })
                .collect::<Vec<_>>();

            let satisfied_slot = rng.gen_range(0..width);
            let satisfied_var = vars[satisfied_slot] as usize - 1;
            clause[satisfied_slot] = if assignment[satisfied_var] {
                vars[satisfied_slot]
            } else {
                -vars[satisfied_slot]
            };

            clauses.push(clause);
        }

        let formula = CnfFormula {
            num_vars: num_vars as u32,
            clauses,
        };
        validate_sat_instance(&formula, &assignment).unwrap()
    }

    fn bench_sat_design(
        instance: &ValidatedSatInstance,
        design: SatDesign,
        rounds: usize,
    ) -> SatBenchResult {
        let circuit = SatCircuit::new_with_design(instance, design);
        let circuit_info = circuit.circuit_info().unwrap();

        let mut total = Duration::ZERO;
        let mut total_proof_bytes = 0usize;

        for _ in 0..rounds {
            let start = Instant::now();
            let param = ProofSystem::setup(&circuit_info, seeded_rng()).unwrap();
            let (prover_param, verifier_param) =
                ProofSystem::preprocess(&param, &circuit_info).unwrap();
            let proof = {
                let mut transcript = Keccak256Transcript::new(());
                ProofSystem::prove_with_shift(
                    &prover_param,
                    &circuit,
                    &mut transcript,
                    seeded_rng(),
                )
                .unwrap();
                transcript.into_proof()
            };
            total += start.elapsed();
            total_proof_bytes += proof.len();

            let mut transcript = Keccak256Transcript::from_proof((), proof.as_slice());
            ProofSystem::verify_with_shift(
                &verifier_param,
                circuit.instances(),
                &mut transcript,
                seeded_rng(),
            )
            .unwrap();
        }

        SatBenchResult {
            avg_prove_ms: total.as_secs_f64() * 1000.0 / rounds as f64,
            avg_proof_bytes: total_proof_bytes / rounds,
            preprocess_cols: circuit_info.preprocess_polys.len(),
            witness_cols: circuit.witness.len(),
            constraints: circuit_info.constraints.len(),
            lookups: circuit_info.lookups.len(),
        }
    }

    fn synthetic_resolution_instance(num_vars: usize) -> ValidatedResolutionInstance {
        let mut clauses = vec![(1..=num_vars as i32).map(|var| -var).collect::<Vec<_>>()];
        clauses.extend((1..=num_vars as i32).map(|var| vec![var]));

        let formula = CnfFormula {
            num_vars: num_vars as u32,
            clauses,
        };

        let mut steps = Vec::with_capacity(num_vars);
        let mut current_parent = 1u32;
        let mut remaining = (1..=num_vars as i32).map(|var| -var).collect::<Vec<_>>();
        for pivot in 1..=num_vars as u32 {
            remaining.retain(|lit| *lit != -(pivot as i32));
            steps.push(ResolutionStep {
                left_parent: pivot + 1,
                right_parent: current_parent,
                pivot_var: pivot,
                resolvent: remaining.clone(),
            });
            current_parent = (num_vars as u32) + 1 + pivot;
        }

        validate_resolution_instance(&formula, ResolutionProof { steps }).unwrap()
    }

    fn bench_resolution_design(
        instance: &ValidatedResolutionInstance,
        design: ResolutionDesign,
        rounds: usize,
    ) -> Result<ResolutionBenchResult, String> {
        let circuit =
            ResolutionCircuit::new_with_design(instance, design).map_err(|err| err.to_string())?;
        let circuit_info = circuit.circuit_info().map_err(|err| format!("{err:?}"))?;

        let mut total = Duration::ZERO;
        let mut total_proof_bytes = 0usize;

        for _ in 0..rounds {
            let start = Instant::now();
            let param = ProofSystem::setup(&circuit_info, seeded_rng())
                .map_err(|err| format!("{err:?}"))?;
            let (prover_param, verifier_param) =
                ProofSystem::preprocess(&param, &circuit_info).map_err(|err| format!("{err:?}"))?;
            let proof = {
                let mut transcript = Keccak256Transcript::new(());
                ProofSystem::prove_with_shift(
                    &prover_param,
                    &circuit,
                    &mut transcript,
                    seeded_rng(),
                )
                .map_err(|err| format!("{err:?}"))?;
                transcript.into_proof()
            };
            total += start.elapsed();
            total_proof_bytes += proof.len();

            let mut transcript = Keccak256Transcript::from_proof((), proof.as_slice());
            ProofSystem::verify_with_shift(
                &verifier_param,
                circuit.instances(),
                &mut transcript,
                seeded_rng(),
            )
            .map_err(|err| format!("{err:?}"))?;
        }

        Ok(ResolutionBenchResult {
            avg_prove_ms: total.as_secs_f64() * 1000.0 / rounds as f64,
            avg_proof_bytes: total_proof_bytes / rounds,
            preprocess_cols: circuit_info.preprocess_polys.len(),
            witness_cols: circuit.witness.len(),
            constraints: circuit_info.constraints.len(),
            lookups: circuit_info.lookups.len(),
            challenges: circuit_info.num_challenges.iter().sum(),
        })
    }

    #[test]
    #[ignore]
    fn benchmark_sat_design_variants() {
        let configs = [
            ("small", 128usize, 256usize, 3usize, 2usize),
            ("medium", 256usize, 1024usize, 4usize, 2usize),
            ("wide", 256usize, 1024usize, 8usize, 2usize),
            ("large", 512usize, 2048usize, 6usize, 2usize),
        ];

        for (name, vars, clauses, width, rounds) in configs {
            let instance =
                synthetic_sat_instance(vars, clauses, width, 1000 + vars as u64 + clauses as u64);
            let split = bench_sat_design(&instance, SatDesign::SplitAssignment, rounds);
            let compact = bench_sat_design(&instance, SatDesign::CompactValue, rounds);
            println!(
                "{name}: split={{ms:{:.2},proof:{},pre:{},wit:{},constraints:{},lookups:{}}} compact={{ms:{:.2},proof:{},pre:{},wit:{},constraints:{},lookups:{}}}",
                split.avg_prove_ms,
                split.avg_proof_bytes,
                split.preprocess_cols,
                split.witness_cols,
                split.constraints,
                split.lookups,
                compact.avg_prove_ms,
                compact.avg_proof_bytes,
                compact.preprocess_cols,
                compact.witness_cols,
                compact.constraints,
                compact.lookups,
            );
        }
    }

    #[test]
    #[ignore]
    fn benchmark_resolution_design_variants() {
        let configs = [
            ("r16", 16usize, 2usize),
            ("r32", 32usize, 2usize),
            ("r48", 48usize, 2usize),
        ];

        for (name, vars, rounds) in configs {
            let instance = synthetic_resolution_instance(vars);
            match bench_resolution_design(&instance, ResolutionDesign::WideLookup, rounds) {
                Ok(wide) => println!(
                    "{name}: wide={{ms:{:.2},proof:{},pre:{},wit:{},constraints:{},lookups:{},ch:{}}}",
                    wide.avg_prove_ms,
                    wide.avg_proof_bytes,
                    wide.preprocess_cols,
                    wide.witness_cols,
                    wide.constraints,
                    wide.lookups,
                    wide.challenges,
                ),
                Err(err) => println!("{name}: wide=ERR({err})"),
            }
            match bench_resolution_design(&instance, ResolutionDesign::EncodedLookup, rounds) {
                Ok(encoded) => println!(
                    "{name}: encoded={{ms:{:.2},proof:{},pre:{},wit:{},constraints:{},lookups:{},ch:{}}}",
                    encoded.avg_prove_ms,
                    encoded.avg_proof_bytes,
                    encoded.preprocess_cols,
                    encoded.witness_cols,
                    encoded.constraints,
                    encoded.lookups,
                    encoded.challenges,
                ),
                Err(err) => println!("{name}: encoded=ERR({err})"),
            }
        }
    }
}
