#![cfg(feature = "backend-plonky3")]

use p3_air::symbolic::{AirLayout, SymbolicAirBuilder};
use p3_air::{Air, AirBuilder, BaseAir, SymbolicExpression, WindowAccess};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_batch_stark::{prove_batch, verify_batch, BatchProof, ProverData, StarkInstance};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_lookup::lookup_traits::{Direction, Lookup};
use p3_lookup::LookupAir;
use p3_lookup_backend::symbolic::{register_send_receive_bus, SymbolicInteraction};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{
    prove_with_preprocessed, setup_preprocessed, verify_with_preprocessed, Proof as UniProof,
    StarkConfig,
};
use rand::{rngs::StdRng, SeedableRng};
use std::panic::{catch_unwind, AssertUnwindSafe};

use crate::backend::phase2::{
    commitment_literal_value, CommittedUnsatPublicStatement, FormulaCommitment,
    UnsatPublicStatement, ValidatedResolutionInstance, ValidatedSatInstance, COMMIT_INDEX_SCALE_A,
    COMMIT_INDEX_SCALE_B, COMMIT_LEN_SCALE_A, COMMIT_LEN_SCALE_B, COMMIT_ROOT_ALPHA_A,
    COMMIT_ROOT_ALPHA_B, COMMIT_SLOT_SCALE_A, COMMIT_SLOT_SCALE_B,
};

type Val = BabyBear;
type Challenge = BinomialExtensionField<Val, 4>;
type Perm = Poseidon2BabyBear<16>;
type Hash = PaddingFreeSponge<Perm, 16, 8, 8>;
type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
type ValMmcs =
    MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, Hash, Compress, 2, 8>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Dft = Radix2DitParallel<Val>;
type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

const FRI_LOG_BLOWUP: usize = 5;
const FRI_MAX_LOG_ARITY: usize = 1;
const FRI_NUM_QUERIES: usize = 8;
const FRI_COMMIT_POW_BITS: usize = 0;
const FRI_QUERY_POW_BITS: usize = 0;
// Keep these tight: the regression test below recomputes both values with
// Plonky3's symbolic evaluator instead of relying on hand-maintained guesses.
const SAT_MAX_CONSTRAINT_DEGREE: usize = 4;
const RESOLUTION_MAX_CONSTRAINT_DEGREE: usize = 9;

pub struct Plonky3SatProof {
    pub proof: UniProof<MyConfig>,
}

pub struct Plonky3ResolutionProof {
    pub proof: BatchProof<MyConfig>,
}

#[derive(Debug, thiserror::Error)]
pub enum Plonky3BackendError {
    #[error("plonky3 received an invalid resolution instance: {0}")]
    InvalidResolutionInstance(String),
    #[error("plonky3 received an invalid public statement: {0}")]
    InvalidPublicStatement(String),
    #[error("plonky3 verification failed: {0:?}")]
    Verification(Box<dyn std::fmt::Debug + Send + Sync>),
}

#[derive(Debug, Clone)]
struct SatAir {
    rows: Vec<SatPreprocessedRow>,
}

#[derive(Debug, Clone)]
struct SatPreprocessedRow {
    is_query: bool,
    is_sorted: bool,
    var_id: u32,
    sign: bool,
    clause_start: bool,
    clause_end: bool,
    same_clause_next: bool,
    same_var_next: bool,
    is_terminal: bool,
}

const SAT_PREP_WIDTH: usize = 9;
const SAT_MAIN_WIDTH: usize = 4;
const SAT_VALUE_COL: usize = 0;
const SAT_TRUTH_COL: usize = 1;
const SAT_PREFIX_OR_COL: usize = 2;
const SAT_PRODUCT_COL: usize = 3;
const SAT_PERM_ALPHA: u32 = 1_000_003;
const SAT_PERM_BETA: u32 = 97_003;
const UNSAT_PUBLIC_VALUES: usize = 3;
const UNSAT_COMMITTED_PUBLIC_VALUES: usize = 5;
const RES_IS_SEMANTIC_COL: usize = 0;
const RES_IS_TABLE_COL: usize = 1;
const RES_IS_QUERY_COL: usize = 2;
const RES_IS_DERIVED_COL: usize = 3;
const RES_ENTRY_ID_COL: usize = 4;
const RES_LEFT_ID_COL: usize = 5;
const RES_RIGHT_ID_COL: usize = 6;
const RES_PIVOT_COL: usize = 7;
const RES_PIVOT_INV_COL: usize = 8;
const RES_COMMIT_ACC_A_COL: usize = 9;
const RES_COMMIT_ACC_B_COL: usize = 10;
const RES_CLAUSE_MULT_COL: usize = 16;
const RES_LEFT_ID_INV_COL: usize = 26;
const RES_RIGHT_ID_INV_COL: usize = 27;
const RES_LEFT_GAP_INV_COL: usize = 28;
const RES_RIGHT_GAP_INV_COL: usize = 29;
const RES_HEADER_WIDTH: usize = 36;
const RES_FP_GAMMA_A: u32 = 1_000_003;
const RES_FP_GAMMA_B: u32 = 1_000_033;
const RES_RANGE_BITS: usize = 29;
const RES_RANGE_LIMB_BITS: usize = 16;
const RES_RANGE_LIMBS: usize = 2;
const RES_RANGE_TABLE_SIZE: usize = 1 << RES_RANGE_LIMB_BITS;
const RES_RANGE_LIMB_BASE: u32 = 1 << RES_RANGE_LIMB_BITS;
const RES_LITERAL_AUX_WIDTH: usize = 2;

#[derive(Debug, Clone)]
struct ResolutionLookupAir {
    formula: crate::backend::cnf::CnfFormula,
    max_width: usize,
    commitment: Option<FormulaCommitment>,
    height: usize,
    num_lookups: usize,
}

const RES_LOOKUP_PREP_FORMULA_ACTIVE_COL: usize = 0;
const RES_LOOKUP_PREP_FORMULA_ID_COL: usize = 1;
const RES_LOOKUP_PREP_FORMULA_LIT_BASE: usize = 2;
const RES_LOOKUP_BUS: &str = "resolution_clause_bus";
const RES_RANGE_BUS: &str = "resolution_range_bus";

fn resolution_clause_bus_interactions(
    formula_values: Vec<SymbolicExpression<Val>>,
    formula_active: SymbolicExpression<Val>,
    clause_mult: SymbolicExpression<Val>,
    derived_values: Vec<SymbolicExpression<Val>>,
    derived_active: SymbolicExpression<Val>,
    left_values: Vec<SymbolicExpression<Val>>,
    right_values: Vec<SymbolicExpression<Val>>,
) -> Vec<SymbolicInteraction<Val>> {
    vec![
        SymbolicInteraction {
            values: formula_values,
            multiplicity: formula_active * clause_mult.clone(),
            direction: Direction::Send,
        },
        SymbolicInteraction {
            values: derived_values,
            multiplicity: derived_active.clone() * clause_mult,
            direction: Direction::Send,
        },
        SymbolicInteraction {
            values: left_values,
            multiplicity: derived_active.clone(),
            direction: Direction::Receive,
        },
        SymbolicInteraction {
            values: right_values,
            multiplicity: derived_active,
            direction: Direction::Receive,
        },
    ]
}

impl<F> BaseAir<F> for SatAir
where
    F: PrimeCharacteristicRing + Send + Sync,
{
    fn width(&self) -> usize {
        SAT_MAIN_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(sat_preprocessed_matrix(&self.rows))
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        (0..SAT_MAIN_WIDTH).collect()
    }

    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        Vec::new()
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(SAT_MAX_CONSTRAINT_DEGREE)
    }
}

impl<AB: AirBuilder> Air<AB> for SatAir
where
    AB::F: PrimeCharacteristicRing + Send + Sync,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let preprocessed = builder.preprocessed();
        let one = AB::Expr::ONE;
        let two = AB::F::from_u64(2);
        let alpha = AB::F::from_u64(SAT_PERM_ALPHA as u64);
        let beta = AB::F::from_u64(SAT_PERM_BETA as u64);

        let value = main.current(SAT_VALUE_COL).unwrap();
        let truth = main.current(SAT_TRUTH_COL).unwrap();
        let prefix_or = main.current(SAT_PREFIX_OR_COL).unwrap();
        let product = main.current(SAT_PRODUCT_COL).unwrap();

        let next_value = main.next(SAT_VALUE_COL).unwrap();
        let next_truth = main.next(SAT_TRUTH_COL).unwrap();
        let next_prefix_or = main.next(SAT_PREFIX_OR_COL).unwrap();
        let next_product = main.next(SAT_PRODUCT_COL).unwrap();

        let is_query = preprocessed.current(0).unwrap();
        let is_sorted = preprocessed.current(1).unwrap();
        let var_id = preprocessed.current(2).unwrap();
        let sign = preprocessed.current(3).unwrap();
        let clause_start = preprocessed.current(4).unwrap();
        let clause_end = preprocessed.current(5).unwrap();
        let same_clause_next = preprocessed.current(6).unwrap();
        let same_var_next = preprocessed.current(7).unwrap();
        let is_terminal = preprocessed.current(8).unwrap();

        let non_value_row = one.clone() - is_query.clone() - is_sorted.clone();
        let not_query = one.clone() - is_query.clone();
        let fingerprint = var_id.clone() + value.clone() * beta + alpha;
        let send_term = one.clone() + is_query.clone() * (fingerprint.clone() - AB::F::ONE);
        let recv_term = one.clone() + is_sorted.clone() * (fingerprint - AB::F::ONE);

        builder
            .when(is_query.clone() + is_sorted.clone())
            .assert_bool(value.clone());
        builder.when(is_query.clone()).assert_bool(truth.clone());
        builder.assert_zero(non_value_row * value.clone());
        builder.assert_zero(not_query.clone() * truth.clone());
        builder.assert_zero(not_query * prefix_or.clone());

        let signed_value = sign.clone() * value.clone();
        let expected_truth = value.clone() + sign.clone() - signed_value * two;
        builder.assert_zero(is_query.clone() * (truth.clone() - expected_truth));
        builder.assert_zero(is_query.clone() * clause_start * (prefix_or.clone() - truth.clone()));
        builder.assert_zero(is_query.clone() * clause_end * (prefix_or.clone() - one.clone()));
        builder.when_transition().assert_zero(
            is_query.clone()
                * same_clause_next
                * (next_prefix_or - (prefix_or.clone() + next_truth - prefix_or * next_truth)),
        );

        builder
            .when_transition()
            .assert_zero(is_sorted.clone() * same_var_next * (next_value - value.clone()));

        builder.when_first_row().assert_one(product.clone());
        builder
            .when_transition()
            .assert_zero(next_product * recv_term - product * send_term);
        builder.assert_zero(is_terminal * (main.current(SAT_PRODUCT_COL).unwrap() - one));
    }
}

impl<F> BaseAir<F> for ResolutionLookupAir
where
    F: PrimeCharacteristicRing + Send + Sync,
{
    fn width(&self) -> usize {
        resolution_trace_width(self.max_width)
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(resolution_lookup_preprocessed_matrix(
            &self.formula,
            self.max_width,
            self.height,
        ))
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        (0..resolution_trace_width(self.max_width)).collect()
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(RESOLUTION_MAX_CONSTRAINT_DEGREE)
    }

    fn num_public_values(&self) -> usize {
        if self.commitment.is_some() {
            UNSAT_COMMITTED_PUBLIC_VALUES
        } else {
            UNSAT_PUBLIC_VALUES
        }
    }
}

impl<AB: AirBuilder> Air<AB> for ResolutionLookupAir
where
    AB::F: PrimeCharacteristicRing + Send + Sync,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let preprocessed = builder.preprocessed();
        let width = resolution_trace_width(self.max_width);
        let current = (0..width)
            .map(|index| main.current(index).unwrap())
            .collect::<Vec<_>>();
        let next = (0..width)
            .map(|index| main.next(index).unwrap())
            .collect::<Vec<_>>();

        let formula_active = preprocessed
            .current(RES_LOOKUP_PREP_FORMULA_ACTIVE_COL)
            .unwrap();
        let formula_id = preprocessed
            .current(RES_LOOKUP_PREP_FORMULA_ID_COL)
            .unwrap();
        let formula_clause = (0..self.max_width)
            .map(|slot| {
                preprocessed
                    .current(RES_LOOKUP_PREP_FORMULA_LIT_BASE + slot)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let next_formula_active = preprocessed
            .next(RES_LOOKUP_PREP_FORMULA_ACTIVE_COL)
            .unwrap();
        let next_formula_id = preprocessed.next(RES_LOOKUP_PREP_FORMULA_ID_COL).unwrap();
        let range_active = preprocessed
            .current(res_lookup_prep_range_active_col(self.max_width))
            .unwrap();

        let is_semantic = current[RES_IS_SEMANTIC_COL].clone();
        let range_table_mult = current[RES_IS_TABLE_COL].clone();
        let is_query = current[RES_IS_QUERY_COL].clone();
        let is_derived = current[RES_IS_DERIVED_COL].clone();
        let entry_id = current[RES_ENTRY_ID_COL].clone();
        let left_id = current[RES_LEFT_ID_COL].clone();
        let right_id = current[RES_RIGHT_ID_COL].clone();
        let pivot = current[RES_PIVOT_COL].clone();
        let pivot_inv = current[RES_PIVOT_INV_COL].clone();
        let commit_acc_a = current[RES_COMMIT_ACC_A_COL].clone();
        let commit_acc_b = current[RES_COMMIT_ACC_B_COL].clone();
        let clause_mult = current[RES_CLAUSE_MULT_COL].clone();
        let left_id_inv = current[RES_LEFT_ID_INV_COL].clone();
        let right_id_inv = current[RES_RIGHT_ID_INV_COL].clone();
        let left_gap_inv = current[RES_LEFT_GAP_INV_COL].clone();
        let right_gap_inv = current[RES_RIGHT_GAP_INV_COL].clone();

        let next_is_semantic = next[RES_IS_SEMANTIC_COL].clone();
        let next_is_derived = next[RES_IS_DERIVED_COL].clone();
        let next_entry_id = next[RES_ENTRY_ID_COL].clone();
        let next_commit_acc_a = next[RES_COMMIT_ACC_A_COL].clone();
        let next_commit_acc_b = next[RES_COMMIT_ACC_B_COL].clone();

        let public_num_vars: AB::Expr = builder.public_values()[0].into();
        let public_num_clauses: AB::Expr = builder.public_values()[1].into();
        let public_max_width: AB::Expr = builder.public_values()[2].into();

        let one = AB::Expr::ONE;
        let current_clause = resolution_clause_exprs(&current, RES_HEADER_WIDTH, self.max_width);
        let left_clause =
            resolution_clause_exprs(&current, RES_HEADER_WIDTH + self.max_width, self.max_width);
        let right_clause = resolution_clause_exprs(
            &current,
            RES_HEADER_WIDTH + self.max_width * 2,
            self.max_width,
        );
        let pivot_delta_limbs = (0..RES_RANGE_LIMBS)
            .map(|limb| current[res_pivot_delta_base(self.max_width) + limb].clone())
            .collect::<Vec<_>>();
        let left_gap_limbs = (0..RES_RANGE_LIMBS)
            .map(|limb| current[res_left_gap_base(self.max_width) + limb].clone())
            .collect::<Vec<_>>();
        let right_gap_limbs = (0..RES_RANGE_LIMBS)
            .map(|limb| current[res_right_gap_base(self.max_width) + limb].clone())
            .collect::<Vec<_>>();

        builder.assert_bool(is_semantic.clone());
        builder.assert_bool(is_derived.clone());
        builder.assert_bool(formula_active.clone());
        builder.assert_bool(range_active.clone());
        builder.assert_zero(is_query.clone());
        builder.assert_zero(
            (one.clone() - AB::Expr::from(range_active.clone())) * range_table_mult.clone(),
        );
        builder.assert_zero(is_derived.clone() * (one.clone() - is_semantic.clone()));
        builder.assert_zero(
            is_semantic.clone()
                * (AB::Expr::from(formula_active.clone()) + is_derived.clone() - one.clone()),
        );
        builder.when_first_row().assert_zero(
            public_num_clauses.clone() - AB::F::from_u64(self.formula.clauses.len() as u64),
        );
        builder
            .when_first_row()
            .assert_zero(public_num_vars.clone() - AB::F::from_u64(self.formula.num_vars as u64));
        builder
            .when_first_row()
            .assert_zero(public_max_width - AB::F::from_u64(self.max_width as u64));
        builder.when_first_row().assert_one(is_semantic.clone());
        builder.when_first_row().assert_one(formula_active.clone());
        builder
            .when_transition()
            .assert_zero(next_is_semantic.clone() * (one.clone() - is_semantic.clone()));

        let current_real_id = AB::Expr::from(formula_active.clone()) * formula_id.clone()
            + is_derived.clone() * entry_id.clone();
        let next_real_id = AB::Expr::from(next_formula_active.clone()) * next_formula_id.clone()
            + next_is_derived.clone() * next_entry_id.clone();
        builder.when_transition().assert_zero(
            next_is_semantic.clone() * (next_real_id - (current_real_id + one.clone())),
        );

        builder.assert_zero(AB::Expr::from(formula_active.clone()) * is_derived.clone());
        builder.assert_zero(
            AB::Expr::from(formula_active.clone()) * (entry_id.clone() - formula_id.clone()),
        );
        if self.commitment.is_none() {
            for (clause_lit, formula_lit) in current_clause.iter().zip(formula_clause.iter()) {
                builder.assert_zero(
                    AB::Expr::from(formula_active.clone())
                        * (clause_lit.clone() - AB::Expr::from(formula_lit.clone())),
                );
            }
        }

        builder.assert_zero((one.clone() - is_derived.clone()) * pivot.clone());
        builder.assert_zero((one.clone() - is_derived.clone()) * pivot_inv.clone());
        builder.assert_zero((one.clone() - is_derived.clone()) * left_id.clone());
        builder.assert_zero((one.clone() - is_derived.clone()) * right_id.clone());
        builder.assert_zero((one.clone() - is_derived.clone()) * left_id_inv.clone());
        builder.assert_zero((one.clone() - is_derived.clone()) * right_id_inv.clone());
        builder.assert_zero((one.clone() - is_derived.clone()) * left_gap_inv.clone());
        builder.assert_zero((one.clone() - is_derived.clone()) * right_gap_inv.clone());
        builder.assert_zero((one.clone() - is_semantic.clone()) * clause_mult.clone());
        for lit in left_clause.iter().chain(right_clause.iter()) {
            builder.assert_zero((one.clone() - is_derived.clone()) * lit.clone());
        }
        for lit in &current_clause {
            builder.assert_zero((one.clone() - is_semantic.clone()) * lit.clone());
        }

        builder.assert_zero(is_derived.clone() * (pivot.clone() * pivot_inv - one.clone()));
        builder.assert_zero(
            is_derived.clone()
                * (pivot.clone() + limbs_to_expr::<AB>(&pivot_delta_limbs)
                    - public_num_vars.clone()),
        );

        let left_gap = limbs_to_expr::<AB>(&left_gap_limbs);
        let right_gap = limbs_to_expr::<AB>(&right_gap_limbs);
        builder.assert_zero(
            is_derived.clone() * (entry_id.clone() - left_id.clone() - left_gap.clone()),
        );
        builder.assert_zero(
            is_derived.clone() * (entry_id.clone() - right_id.clone() - right_gap.clone()),
        );
        builder.assert_zero(is_derived.clone() * (left_id.clone() * left_id_inv - one.clone()));
        builder.assert_zero(is_derived.clone() * (right_id.clone() * right_id_inv - one.clone()));
        builder.assert_zero(is_derived.clone() * (left_gap.clone() * left_gap_inv - one.clone()));
        builder.assert_zero(is_derived.clone() * (right_gap.clone() * right_gap_inv - one.clone()));

        let mut left_zero_flags = Vec::with_capacity(self.max_width);
        let mut right_zero_flags = Vec::with_capacity(self.max_width);
        let mut res_zero_flags = Vec::with_capacity(self.max_width);
        let mut left_pivot_flags = Vec::with_capacity(self.max_width);
        let mut right_neg_pivot_flags = Vec::with_capacity(self.max_width);
        let mut left_keep_flags = Vec::with_capacity(self.max_width);
        let mut right_keep_flags = Vec::with_capacity(self.max_width);
        let mut left_source_counts = Vec::with_capacity(self.max_width);
        let mut left_selected_counts = Vec::with_capacity(self.max_width);
        let mut right_source_counts = Vec::with_capacity(self.max_width);
        let mut right_selected_counts = Vec::with_capacity(self.max_width);
        let mut left_source_prod_a = Vec::with_capacity(self.max_width);
        let mut left_source_prod_b = Vec::with_capacity(self.max_width);
        let mut left_selected_prod_a = Vec::with_capacity(self.max_width);
        let mut left_selected_prod_b = Vec::with_capacity(self.max_width);
        let mut right_source_prod_a = Vec::with_capacity(self.max_width);
        let mut right_source_prod_b = Vec::with_capacity(self.max_width);
        let mut right_selected_prod_a = Vec::with_capacity(self.max_width);
        let mut right_selected_prod_b = Vec::with_capacity(self.max_width);

        for i in 0..self.max_width {
            let left = left_clause[i].clone();
            let right = right_clause[i].clone();
            let res = current_clause[i].clone();
            let current_aux_base = res_literal_aux_base(self.max_width, 0, i);
            let left_aux_base = res_literal_aux_base(self.max_width, 1, i);
            let right_aux_base = res_literal_aux_base(self.max_width, 2, i);

            let current_is_zero = current[current_aux_base].clone();
            let current_inv = current[current_aux_base + 1].clone();
            constrain_resolution_literal_zero::<AB>(
                builder,
                res.clone(),
                current_is_zero.clone(),
                current_inv,
            );

            let left_is_zero = current[left_aux_base].clone();
            let left_inv = current[left_aux_base + 1].clone();
            constrain_resolution_literal_zero::<AB>(
                builder,
                left.clone(),
                left_is_zero.clone(),
                left_inv,
            );

            let right_is_zero = current[right_aux_base].clone();
            let right_inv = current[right_aux_base + 1].clone();
            constrain_resolution_literal_zero::<AB>(
                builder,
                right.clone(),
                right_is_zero.clone(),
                right_inv,
            );

            let left_pivot_flag = current[res_left_pivot_eq_base(self.max_width) + i].clone();
            let left_pivot_inv = current[res_left_pivot_inv_base(self.max_width) + i].clone();
            let right_neg_pivot_flag =
                current[res_right_neg_pivot_eq_base(self.max_width) + i].clone();
            let right_neg_pivot_inv =
                current[res_right_neg_pivot_inv_base(self.max_width) + i].clone();
            let left_keep = current[res_left_keep_base(self.max_width) + i].clone();
            let right_keep = current[res_right_keep_base(self.max_width) + i].clone();

            builder.assert_bool(left_pivot_flag.clone());
            builder.assert_bool(right_neg_pivot_flag.clone());
            builder.assert_bool(left_keep.clone());
            builder.assert_bool(right_keep.clone());
            builder.assert_zero((one.clone() - is_derived.clone()) * left_pivot_flag.clone());
            builder.assert_zero((one.clone() - is_derived.clone()) * left_pivot_inv.clone());
            builder.assert_zero((one.clone() - is_derived.clone()) * right_neg_pivot_flag.clone());
            builder.assert_zero((one.clone() - is_derived.clone()) * right_neg_pivot_inv.clone());
            builder.assert_zero((one.clone() - is_derived.clone()) * left_keep.clone());
            builder.assert_zero((one.clone() - is_derived.clone()) * right_keep.clone());

            builder.assert_zero(
                is_derived.clone() * left_pivot_flag.clone() * (left.clone() - pivot.clone()),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (one.clone() - left_pivot_flag.clone())
                    * ((left.clone() - pivot.clone()) * left_pivot_inv - one.clone()),
            );
            builder.assert_zero(
                is_derived.clone() * right_neg_pivot_flag.clone() * (right.clone() + pivot.clone()),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (one.clone() - right_neg_pivot_flag.clone())
                    * ((right.clone() + pivot.clone()) * right_neg_pivot_inv - one.clone()),
            );

            builder.assert_zero(left_keep.clone() * current_is_zero.clone());
            builder.assert_zero(right_keep.clone() * current_is_zero.clone());

            let res_active =
                is_derived.clone() * (one.clone() - AB::Expr::from(current_is_zero.clone()));
            builder.assert_zero(
                res_active.clone()
                    * (one.clone() - left_keep.clone())
                    * (one.clone() - right_keep.clone()),
            );

            left_zero_flags.push(AB::Expr::from(left_is_zero));
            right_zero_flags.push(AB::Expr::from(right_is_zero));
            res_zero_flags.push(AB::Expr::from(current_is_zero));
            left_pivot_flags.push(AB::Expr::from(left_pivot_flag));
            right_neg_pivot_flags.push(AB::Expr::from(right_neg_pivot_flag));
            left_keep_flags.push(AB::Expr::from(left_keep));
            right_keep_flags.push(AB::Expr::from(right_keep));
            left_source_counts
                .push(current[res_left_source_count_base(self.max_width) + i].clone());
            left_selected_counts
                .push(current[res_left_selected_count_base(self.max_width) + i].clone());
            right_source_counts
                .push(current[res_right_source_count_base(self.max_width) + i].clone());
            right_selected_counts
                .push(current[res_right_selected_count_base(self.max_width) + i].clone());
            left_source_prod_a
                .push(current[res_left_source_prod_a_base(self.max_width) + i].clone());
            left_source_prod_b
                .push(current[res_left_source_prod_b_base(self.max_width) + i].clone());
            left_selected_prod_a
                .push(current[res_left_selected_prod_a_base(self.max_width) + i].clone());
            left_selected_prod_b
                .push(current[res_left_selected_prod_b_base(self.max_width) + i].clone());
            right_source_prod_a
                .push(current[res_right_source_prod_a_base(self.max_width) + i].clone());
            right_source_prod_b
                .push(current[res_right_source_prod_b_base(self.max_width) + i].clone());
            right_selected_prod_a
                .push(current[res_right_selected_prod_a_base(self.max_width) + i].clone());
            right_selected_prod_b
                .push(current[res_right_selected_prod_b_base(self.max_width) + i].clone());
        }

        if let Some(commitment) = &self.commitment {
            let public_mix_a: AB::Expr = builder.public_values()[3].into();
            let public_mix_b: AB::Expr = builder.public_values()[4].into();
            let commitment_width = commitment.max_clause_width as usize;

            builder.when_first_row().assert_zero(commit_acc_a.clone());
            builder.when_first_row().assert_zero(commit_acc_b.clone());

            let mut clause_len = AB::Expr::ZERO;
            let mut clause_mix_a = entry_id.clone() * AB::F::from_u64(COMMIT_INDEX_SCALE_A);
            let mut clause_mix_b = entry_id.clone() * AB::F::from_u64(COMMIT_INDEX_SCALE_B);

            for i in 0..self.max_width {
                if i < commitment_width {
                    let is_nonzero = one.clone() - res_zero_flags[i].clone();
                    clause_len = clause_len + is_nonzero;
                    let weight_a = AB::F::from_u64(((i + 1) as u64) * COMMIT_SLOT_SCALE_A);
                    let weight_b = AB::F::from_u64(((i + 1) as u64) * COMMIT_SLOT_SCALE_B);
                    clause_mix_a = clause_mix_a + current_clause[i].clone() * weight_a;
                    clause_mix_b = clause_mix_b + current_clause[i].clone() * weight_b;
                } else {
                    builder.assert_zero(
                        AB::Expr::from(formula_active.clone()) * current_clause[i].clone(),
                    );
                }
            }

            clause_mix_a = clause_mix_a + clause_len.clone() * AB::F::from_u64(COMMIT_LEN_SCALE_A);
            clause_mix_b = clause_mix_b + clause_len * AB::F::from_u64(COMMIT_LEN_SCALE_B);

            builder.when_transition().assert_zero(
                AB::Expr::from(formula_active.clone())
                    * (next_commit_acc_a.clone()
                        - (commit_acc_a * AB::F::from_u64(COMMIT_ROOT_ALPHA_A) + clause_mix_a)),
            );
            builder.when_transition().assert_zero(
                AB::Expr::from(formula_active.clone())
                    * (next_commit_acc_b.clone()
                        - (commit_acc_b * AB::F::from_u64(COMMIT_ROOT_ALPHA_B) + clause_mix_b)),
            );

            let formula_end =
                AB::Expr::from(formula_active.clone()) * (one.clone() - next_formula_active);
            builder
                .when_transition()
                .assert_zero(formula_end.clone() * (next_commit_acc_a - public_mix_a));
            builder
                .when_transition()
                .assert_zero(formula_end * (next_commit_acc_b - public_mix_b));
        }

        let gamma_a: AB::Expr = AB::F::from_u64(RES_FP_GAMMA_A as u64).into();
        let gamma_b: AB::Expr = AB::F::from_u64(RES_FP_GAMMA_B as u64).into();
        let mut left_pivot_count = AB::Expr::ZERO;
        let mut right_neg_pivot_count = AB::Expr::ZERO;
        for i in 0..self.max_width {
            let left_active = is_derived.clone()
                * (one.clone() - left_zero_flags[i].clone())
                * (one.clone() - left_pivot_flags[i].clone());
            let right_active = is_derived.clone()
                * (one.clone() - right_zero_flags[i].clone())
                * (one.clone() - right_neg_pivot_flags[i].clone());
            let left_selected = left_keep_flags[i].clone();
            let right_selected = right_keep_flags[i].clone();

            left_pivot_count = left_pivot_count + left_pivot_flags[i].clone();
            right_neg_pivot_count = right_neg_pivot_count + right_neg_pivot_flags[i].clone();

            let left_source_count_expected = if i == 0 {
                left_active.clone()
            } else {
                left_source_counts[i - 1].clone().into() + left_active.clone()
            };
            let left_selected_count_expected = if i == 0 {
                left_selected.clone()
            } else {
                left_selected_counts[i - 1].clone().into() + left_selected.clone()
            };
            let right_source_count_expected = if i == 0 {
                right_active.clone()
            } else {
                right_source_counts[i - 1].clone().into() + right_active.clone()
            };
            let right_selected_count_expected = if i == 0 {
                right_selected.clone()
            } else {
                right_selected_counts[i - 1].clone().into() + right_selected.clone()
            };

            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(left_source_counts[i].clone()) - left_source_count_expected),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(left_selected_counts[i].clone())
                        - left_selected_count_expected),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(right_source_counts[i].clone())
                        - right_source_count_expected),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(right_selected_counts[i].clone())
                        - right_selected_count_expected),
            );

            let left_source_term_a = one.clone()
                + left_active.clone() * (gamma_a.clone() - left_clause[i].clone() - one.clone());
            let left_source_term_b = one.clone()
                + left_active.clone() * (gamma_b.clone() - left_clause[i].clone() - one.clone());
            let left_selected_term_a = one.clone()
                + left_selected.clone()
                    * (gamma_a.clone() - current_clause[i].clone() - one.clone());
            let left_selected_term_b = one.clone()
                + left_selected.clone()
                    * (gamma_b.clone() - current_clause[i].clone() - one.clone());
            let right_source_term_a = one.clone()
                + right_active.clone() * (gamma_a.clone() - right_clause[i].clone() - one.clone());
            let right_source_term_b = one.clone()
                + right_active.clone() * (gamma_b.clone() - right_clause[i].clone() - one.clone());
            let right_selected_term_a = one.clone()
                + right_selected.clone()
                    * (gamma_a.clone() - current_clause[i].clone() - one.clone());
            let right_selected_term_b = one.clone()
                + right_selected.clone()
                    * (gamma_b.clone() - current_clause[i].clone() - one.clone());

            let left_source_prod_a_expected = if i == 0 {
                left_source_term_a
            } else {
                AB::Expr::from(left_source_prod_a[i - 1].clone()) * left_source_term_a
            };
            let left_source_prod_b_expected = if i == 0 {
                left_source_term_b
            } else {
                AB::Expr::from(left_source_prod_b[i - 1].clone()) * left_source_term_b
            };
            let left_selected_prod_a_expected = if i == 0 {
                left_selected_term_a
            } else {
                AB::Expr::from(left_selected_prod_a[i - 1].clone()) * left_selected_term_a
            };
            let left_selected_prod_b_expected = if i == 0 {
                left_selected_term_b
            } else {
                AB::Expr::from(left_selected_prod_b[i - 1].clone()) * left_selected_term_b
            };
            let right_source_prod_a_expected = if i == 0 {
                right_source_term_a
            } else {
                AB::Expr::from(right_source_prod_a[i - 1].clone()) * right_source_term_a
            };
            let right_source_prod_b_expected = if i == 0 {
                right_source_term_b
            } else {
                AB::Expr::from(right_source_prod_b[i - 1].clone()) * right_source_term_b
            };
            let right_selected_prod_a_expected = if i == 0 {
                right_selected_term_a
            } else {
                AB::Expr::from(right_selected_prod_a[i - 1].clone()) * right_selected_term_a
            };
            let right_selected_prod_b_expected = if i == 0 {
                right_selected_term_b
            } else {
                AB::Expr::from(right_selected_prod_b[i - 1].clone()) * right_selected_term_b
            };

            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(left_source_prod_a[i].clone()) - left_source_prod_a_expected),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(left_source_prod_b[i].clone()) - left_source_prod_b_expected),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(left_selected_prod_a[i].clone())
                        - left_selected_prod_a_expected),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(left_selected_prod_b[i].clone())
                        - left_selected_prod_b_expected),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(right_source_prod_a[i].clone())
                        - right_source_prod_a_expected),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(right_source_prod_b[i].clone())
                        - right_source_prod_b_expected),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(right_selected_prod_a[i].clone())
                        - right_selected_prod_a_expected),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(right_selected_prod_b[i].clone())
                        - right_selected_prod_b_expected),
            );
        }

        if self.max_width > 0 {
            let last = self.max_width - 1;
            builder.assert_zero(is_derived.clone() * (left_pivot_count - one.clone()));
            builder.assert_zero(is_derived.clone() * (right_neg_pivot_count - one.clone()));
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(left_source_counts[last].clone())
                        - AB::Expr::from(left_selected_counts[last].clone())),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(right_source_counts[last].clone())
                        - AB::Expr::from(right_selected_counts[last].clone())),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(left_source_prod_a[last].clone())
                        - AB::Expr::from(left_selected_prod_a[last].clone())),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(left_source_prod_b[last].clone())
                        - AB::Expr::from(left_selected_prod_b[last].clone())),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(right_source_prod_a[last].clone())
                        - AB::Expr::from(right_selected_prod_a[last].clone())),
            );
            builder.assert_zero(
                is_derived.clone()
                    * (AB::Expr::from(right_source_prod_b[last].clone())
                        - AB::Expr::from(right_selected_prod_b[last].clone())),
            );
        }

        let semantic_end = is_semantic.clone() * (one.clone() - next_is_semantic.clone());
        builder.assert_zero(semantic_end.clone() * (one.clone() - is_derived.clone()));
        for lit in &current_clause {
            builder.assert_zero(semantic_end.clone() * lit.clone());
        }
    }
}

impl LookupAir<Val> for ResolutionLookupAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<Lookup<Val>> {
        self.num_lookups = 0;

        let symbolic_builder = SymbolicAirBuilder::<Val, Challenge>::new(AirLayout {
            preprocessed_width: self.max_width + 4,
            main_width: resolution_trace_width(self.max_width),
            num_public_values: if self.commitment.is_some() {
                UNSAT_COMMITTED_PUBLIC_VALUES
            } else {
                UNSAT_PUBLIC_VALUES
            },
            ..Default::default()
        });

        let preprocessed = symbolic_builder.preprocessed();
        let main = symbolic_builder.main();
        let prep_row = preprocessed.current_slice();
        let main_row = main.current_slice();

        let formula_active: SymbolicExpression<Val> =
            prep_row[RES_LOOKUP_PREP_FORMULA_ACTIVE_COL].into();
        let clause_mult: SymbolicExpression<Val> = main_row[RES_CLAUSE_MULT_COL].into();
        let formula_values = if self.commitment.is_some() {
            std::iter::once(main_row[RES_ENTRY_ID_COL].into())
                .chain((0..self.max_width).map(|slot| main_row[RES_HEADER_WIDTH + slot].into()))
                .collect::<Vec<SymbolicExpression<Val>>>()
        } else {
            std::iter::once(prep_row[RES_LOOKUP_PREP_FORMULA_ID_COL].into())
                .chain(
                    (0..self.max_width)
                        .map(|slot| prep_row[RES_LOOKUP_PREP_FORMULA_LIT_BASE + slot].into()),
                )
                .collect::<Vec<SymbolicExpression<Val>>>()
        };

        let derived_active: SymbolicExpression<Val> = main_row[RES_IS_DERIVED_COL].into();
        let derived_values = std::iter::once(main_row[RES_ENTRY_ID_COL].into())
            .chain((0..self.max_width).map(|slot| main_row[RES_HEADER_WIDTH + slot].into()))
            .collect::<Vec<SymbolicExpression<Val>>>();
        let left_values = std::iter::once(main_row[RES_LEFT_ID_COL].into())
            .chain(
                (0..self.max_width)
                    .map(|slot| main_row[RES_HEADER_WIDTH + self.max_width + slot].into()),
            )
            .collect::<Vec<SymbolicExpression<Val>>>();
        let right_values = std::iter::once(main_row[RES_RIGHT_ID_COL].into())
            .chain(
                (0..self.max_width)
                    .map(|slot| main_row[RES_HEADER_WIDTH + self.max_width * 2 + slot].into()),
            )
            .collect::<Vec<SymbolicExpression<Val>>>();

        // The clause bus is a direct tuple-based send/receive interaction:
        // formula clauses and derived clauses send with multiplicity equal to
        // the number of times they are referenced as parents, while each
        // parent reference receives once. Since `(clause_id, lits...)` is
        // unique per clause, the global lookup enforces exact parent usage.
        let clause_interactions = resolution_clause_bus_interactions(
            formula_values,
            formula_active,
            clause_mult,
            derived_values,
            derived_active,
            left_values,
            right_values,
        );
        let range_active: SymbolicExpression<Val> =
            prep_row[res_lookup_prep_range_active_col(self.max_width)].into();
        let range_value: SymbolicExpression<Val> =
            prep_row[res_lookup_prep_range_value_col(self.max_width)].into();
        let range_mult: SymbolicExpression<Val> = main_row[RES_IS_TABLE_COL].into();

        let mut range_interactions = vec![SymbolicInteraction {
            values: vec![range_value],
            multiplicity: range_active * range_mult,
            direction: Direction::Send,
        }];
        range_interactions.extend([
            SymbolicInteraction {
                values: vec![main_row[res_pivot_delta_base(self.max_width)].into()],
                multiplicity: main_row[RES_IS_DERIVED_COL].into(),
                direction: Direction::Receive,
            },
            SymbolicInteraction {
                values: vec![main_row[res_pivot_delta_base(self.max_width) + 1].into()],
                multiplicity: main_row[RES_IS_DERIVED_COL].into(),
                direction: Direction::Receive,
            },
            SymbolicInteraction {
                values: vec![main_row[res_left_gap_base(self.max_width)].into()],
                multiplicity: main_row[RES_IS_DERIVED_COL].into(),
                direction: Direction::Receive,
            },
            SymbolicInteraction {
                values: vec![main_row[res_left_gap_base(self.max_width) + 1].into()],
                multiplicity: main_row[RES_IS_DERIVED_COL].into(),
                direction: Direction::Receive,
            },
            SymbolicInteraction {
                values: vec![main_row[res_right_gap_base(self.max_width)].into()],
                multiplicity: main_row[RES_IS_DERIVED_COL].into(),
                direction: Direction::Receive,
            },
            SymbolicInteraction {
                values: vec![main_row[res_right_gap_base(self.max_width) + 1].into()],
                multiplicity: main_row[RES_IS_DERIVED_COL].into(),
                direction: Direction::Receive,
            },
        ]);
        vec![
            register_send_receive_bus(self, RES_LOOKUP_BUS.to_owned(), &clause_interactions),
            register_send_receive_bus(self, RES_RANGE_BUS.to_owned(), &range_interactions),
        ]
    }
}

pub fn prove_sat(instance: &ValidatedSatInstance) -> Result<Plonky3SatProof, Plonky3BackendError> {
    let air = sat_air(instance);
    let trace = sat_trace(instance, &air.rows);
    let config = make_config();
    let degree_bits = trace.height().ilog2() as usize;
    let (preprocessed_prover_data, preprocessed_vk) =
        setup_preprocessed::<MyConfig, _>(&config, &air, degree_bits)
            .expect("sat air always defines preprocessed columns");
    let proof = catch_unwind(AssertUnwindSafe(|| {
        prove_with_preprocessed(&config, &air, trace, &[], Some(&preprocessed_prover_data))
    }))
    .map_err(panic_as_plonky3_error)?;
    catch_unwind(AssertUnwindSafe(|| {
        verify_with_preprocessed(&config, &air, &proof, &[], Some(&preprocessed_vk))
    }))
    .map_err(panic_as_plonky3_error)?
    .map_err(|err| Plonky3BackendError::Verification(Box::new(err)))?;
    Ok(Plonky3SatProof { proof })
}

pub fn verify_sat(
    instance: &ValidatedSatInstance,
    proof: &Plonky3SatProof,
) -> Result<(), Plonky3BackendError> {
    let air = sat_air(instance);
    let config = make_config();
    let trace_height = sat_trace_height(instance);
    let degree_bits = trace_height.ilog2() as usize;
    let (_, preprocessed_vk) = setup_preprocessed::<MyConfig, _>(&config, &air, degree_bits)
        .expect("sat air always defines preprocessed columns");
    catch_unwind(AssertUnwindSafe(|| {
        verify_with_preprocessed(&config, &air, &proof.proof, &[], Some(&preprocessed_vk))
    }))
    .map_err(panic_as_plonky3_error)?
    .map_err(|err| Plonky3BackendError::Verification(Box::new(err)))
}

pub fn prove_unsat(
    instance: &ValidatedResolutionInstance,
) -> Result<Plonky3ResolutionProof, Plonky3BackendError> {
    prove_unsat_with_lookup(instance)
}

pub fn prove_unsat_committed(
    instance: &ValidatedResolutionInstance,
) -> Result<Plonky3ResolutionProof, Plonky3BackendError> {
    prove_unsat_with_committed_lookup(instance)
}

pub fn verify_unsat(
    statement: &UnsatPublicStatement,
    proof: &Plonky3ResolutionProof,
) -> Result<(), Plonky3BackendError> {
    verify_unsat_with_lookup(statement, proof)
}

pub fn verify_unsat_committed(
    statement: &CommittedUnsatPublicStatement,
    proof: &Plonky3ResolutionProof,
) -> Result<(), Plonky3BackendError> {
    verify_unsat_with_committed_lookup(statement, proof)
}

fn prove_unsat_with_lookup(
    instance: &ValidatedResolutionInstance,
) -> Result<Plonky3ResolutionProof, Plonky3BackendError> {
    validate_resolution_shape(instance)?;
    let statement = instance.public_statement();
    let trace = resolution_lookup_trace::<Val>(instance, &statement);
    let degree_bits = trace.height().ilog2() as usize;
    let mut airs = vec![resolution_lookup_air(&statement, trace.height())];
    let config = make_config();
    let public_values = resolution_public_values(&statement);
    let prover_data = ProverData::from_airs_and_degrees(&config, &mut airs, &[degree_bits]);
    let common = &prover_data.common;
    let trace_refs = vec![&trace];
    let instances =
        StarkInstance::new_multiple(&airs, &trace_refs, &[public_values.clone()], common);
    let proof = catch_unwind(AssertUnwindSafe(|| {
        prove_batch(&config, &instances, &prover_data)
    }))
    .map_err(panic_as_plonky3_error)?;
    let result = Plonky3ResolutionProof { proof };
    verify_unsat_with_lookup(&statement, &result)?;
    Ok(result)
}

fn prove_unsat_with_committed_lookup(
    instance: &ValidatedResolutionInstance,
) -> Result<Plonky3ResolutionProof, Plonky3BackendError> {
    validate_resolution_shape(instance)?;
    let statement = instance.committed_public_statement();
    validate_committed_statement(&statement)?;
    let trace_statement = instance.public_statement();
    let trace = resolution_lookup_trace::<Val>(instance, &trace_statement);
    let degree_bits = trace.height().ilog2() as usize;
    let mut airs = vec![resolution_lookup_air_committed(&statement, trace.height())];
    let config = make_config();
    let public_values = resolution_committed_public_values(&statement);
    let prover_data = ProverData::from_airs_and_degrees(&config, &mut airs, &[degree_bits]);
    let common = &prover_data.common;
    let trace_refs = vec![&trace];
    let instances =
        StarkInstance::new_multiple(&airs, &trace_refs, &[public_values.clone()], common);
    let proof = catch_unwind(AssertUnwindSafe(|| {
        prove_batch(&config, &instances, &prover_data)
    }))
    .map_err(panic_as_plonky3_error)?;
    let result = Plonky3ResolutionProof { proof };
    verify_unsat_with_committed_lookup(&statement, &result)?;
    Ok(result)
}

fn validate_resolution_shape(
    instance: &ValidatedResolutionInstance,
) -> Result<(), Plonky3BackendError> {
    if instance.commitment.num_vars >= (1u32 << RES_RANGE_BITS) {
        return Err(Plonky3BackendError::InvalidPublicStatement(format!(
            "num_vars {} exceeds plonky3 range-check limit {}",
            instance.commitment.num_vars,
            (1u32 << RES_RANGE_BITS) - 1
        )));
    }
    let total_clauses = instance.formula.clauses.len()
        + instance
            .proof
            .steps
            .len()
            .max(instance.expanded_steps.len());
    if total_clauses >= (1usize << RES_RANGE_BITS) {
        return Err(Plonky3BackendError::InvalidResolutionInstance(format!(
            "resolution trace needs {total_clauses} clauses, exceeding plonky3 id range {}",
            (1usize << RES_RANGE_BITS) - 1
        )));
    }
    Ok(())
}

fn verify_unsat_with_lookup(
    statement: &UnsatPublicStatement,
    proof: &Plonky3ResolutionProof,
) -> Result<(), Plonky3BackendError> {
    let Some(&degree_bits) = proof.proof.degree_bits.first() else {
        return Err(Plonky3BackendError::Verification(Box::new(
            "missing degree bits for resolution proof".to_owned(),
        )));
    };
    let height = 1usize << degree_bits;
    let mut airs = vec![resolution_lookup_air(statement, height)];
    let config = make_config();
    let public_values = vec![resolution_public_values(statement)];
    let prover_data = ProverData::from_airs_and_degrees(&config, &mut airs, &[degree_bits]);
    let common = &prover_data.common;
    verify_batch(&config, &airs, &proof.proof, &public_values, common)
        .map_err(|err| Plonky3BackendError::Verification(Box::new(err)))?;
    Ok(())
}

fn verify_unsat_with_committed_lookup(
    statement: &CommittedUnsatPublicStatement,
    proof: &Plonky3ResolutionProof,
) -> Result<(), Plonky3BackendError> {
    validate_committed_statement(statement)?;
    let Some(&degree_bits) = proof.proof.degree_bits.first() else {
        return Err(Plonky3BackendError::Verification(Box::new(
            "missing degree bits for resolution proof".to_owned(),
        )));
    };
    let height = 1usize << degree_bits;
    let mut airs = vec![resolution_lookup_air_committed(statement, height)];
    let config = make_config();
    let public_values = vec![resolution_committed_public_values(statement)];
    let prover_data = ProverData::from_airs_and_degrees(&config, &mut airs, &[degree_bits]);
    let common = &prover_data.common;
    verify_batch(&config, &airs, &proof.proof, &public_values, common)
        .map_err(|err| Plonky3BackendError::Verification(Box::new(err)))?;
    Ok(())
}

fn resolution_lookup_air(statement: &UnsatPublicStatement, height: usize) -> ResolutionLookupAir {
    ResolutionLookupAir {
        formula: normalize_resolution_air_formula(&statement.formula),
        max_width: statement.max_clause_width.max(1) as usize,
        commitment: None,
        height,
        num_lookups: 0,
    }
}

fn resolution_lookup_air_committed(
    statement: &CommittedUnsatPublicStatement,
    height: usize,
) -> ResolutionLookupAir {
    ResolutionLookupAir {
        formula: crate::backend::cnf::CnfFormula {
            num_vars: statement.commitment.num_vars,
            clauses: vec![Vec::new(); statement.commitment.num_clauses as usize],
        },
        max_width: statement.air_max_clause_width.max(1) as usize,
        commitment: Some(statement.commitment.clone()),
        height,
        num_lookups: 0,
    }
}

fn sat_air(instance: &ValidatedSatInstance) -> SatAir {
    SatAir {
        rows: sat_rows(instance),
    }
}

fn resolution_public_values(statement: &UnsatPublicStatement) -> Vec<Val> {
    vec![
        Val::from_u64(statement.num_vars as u64),
        Val::from_u64(statement.num_clauses as u64),
        Val::from_u64(statement.max_clause_width as u64),
    ]
}

fn resolution_committed_public_values(statement: &CommittedUnsatPublicStatement) -> Vec<Val> {
    vec![
        Val::from_u64(statement.commitment.num_vars as u64),
        Val::from_u64(statement.commitment.num_clauses as u64),
        Val::from_u64(statement.air_max_clause_width as u64),
        Val::from_u64(statement.commitment.mix_a as u64),
        Val::from_u64(statement.commitment.mix_b as u64),
    ]
}

fn validate_committed_statement(
    statement: &CommittedUnsatPublicStatement,
) -> Result<(), Plonky3BackendError> {
    if statement.commitment.max_clause_width > statement.air_max_clause_width {
        return Err(Plonky3BackendError::InvalidPublicStatement(format!(
            "commitment width {} exceeds AIR width {}",
            statement.commitment.max_clause_width, statement.air_max_clause_width
        )));
    }
    Ok(())
}

fn panic_as_plonky3_error(payload: Box<dyn std::any::Any + Send>) -> Plonky3BackendError {
    let message = if let Some(message) = payload.downcast_ref::<&'static str>() {
        (*message).to_owned()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "plonky3 panicked while processing the witness".to_owned()
    };
    Plonky3BackendError::Verification(Box::new(message))
}

fn resolution_clause_exprs<E: Clone>(row: &[E], base: usize, width: usize) -> Vec<E> {
    (0..width).map(|slot| row[base + slot].clone()).collect()
}

fn normalize_resolution_air_formula(
    formula: &crate::backend::cnf::CnfFormula,
) -> crate::backend::cnf::CnfFormula {
    crate::backend::cnf::CnfFormula {
        num_vars: formula.num_vars,
        clauses: formula
            .clauses
            .iter()
            .map(|clause| normalize_resolution_air_clause(clause))
            .collect(),
    }
}

fn normalize_resolution_air_clause(clause: &[i32]) -> Vec<i32> {
    let mut normalized = clause.to_vec();
    normalized.sort_unstable();
    normalized.dedup();
    normalized
}

fn resolution_trace_width(max_width: usize) -> usize {
    res_right_selected_prod_b_base(max_width) + max_width
}

fn res_lookup_prep_range_active_col(max_width: usize) -> usize {
    RES_LOOKUP_PREP_FORMULA_LIT_BASE + max_width
}

fn res_lookup_prep_range_value_col(max_width: usize) -> usize {
    res_lookup_prep_range_active_col(max_width) + 1
}

fn res_literal_aux_end(max_width: usize) -> usize {
    RES_HEADER_WIDTH
        + max_width * 3
        + RES_RANGE_LIMBS
        + RES_RANGE_LIMBS
        + RES_RANGE_LIMBS
        + max_width * 3 * RES_LITERAL_AUX_WIDTH
}

fn res_pivot_delta_base(max_width: usize) -> usize {
    RES_HEADER_WIDTH + max_width * 3
}

fn res_left_gap_base(max_width: usize) -> usize {
    res_pivot_delta_base(max_width) + RES_RANGE_LIMBS
}

fn res_right_gap_base(max_width: usize) -> usize {
    res_left_gap_base(max_width) + RES_RANGE_LIMBS
}

fn res_literal_aux_base(max_width: usize, clause_block: usize, slot: usize) -> usize {
    res_right_gap_base(max_width)
        + RES_RANGE_LIMBS
        + (clause_block * max_width + slot) * RES_LITERAL_AUX_WIDTH
}

fn res_left_pivot_eq_base(max_width: usize) -> usize {
    res_literal_aux_end(max_width)
}

fn res_left_pivot_inv_base(max_width: usize) -> usize {
    res_left_pivot_eq_base(max_width) + max_width
}

fn res_right_neg_pivot_eq_base(max_width: usize) -> usize {
    res_left_pivot_inv_base(max_width) + max_width
}

fn res_right_neg_pivot_inv_base(max_width: usize) -> usize {
    res_right_neg_pivot_eq_base(max_width) + max_width
}

fn res_left_keep_base(max_width: usize) -> usize {
    res_right_neg_pivot_inv_base(max_width) + max_width
}

fn res_right_keep_base(max_width: usize) -> usize {
    res_left_keep_base(max_width) + max_width
}

fn res_left_source_count_base(max_width: usize) -> usize {
    res_right_keep_base(max_width) + max_width
}

fn res_left_selected_count_base(max_width: usize) -> usize {
    res_left_source_count_base(max_width) + max_width
}

fn res_right_source_count_base(max_width: usize) -> usize {
    res_left_selected_count_base(max_width) + max_width
}

fn res_right_selected_count_base(max_width: usize) -> usize {
    res_right_source_count_base(max_width) + max_width
}

fn res_left_source_prod_a_base(max_width: usize) -> usize {
    res_right_selected_count_base(max_width) + max_width
}

fn res_left_source_prod_b_base(max_width: usize) -> usize {
    res_left_source_prod_a_base(max_width) + max_width
}

fn res_left_selected_prod_a_base(max_width: usize) -> usize {
    res_left_source_prod_b_base(max_width) + max_width
}

fn res_left_selected_prod_b_base(max_width: usize) -> usize {
    res_left_selected_prod_a_base(max_width) + max_width
}

fn res_right_source_prod_a_base(max_width: usize) -> usize {
    res_left_selected_prod_b_base(max_width) + max_width
}

fn res_right_source_prod_b_base(max_width: usize) -> usize {
    res_right_source_prod_a_base(max_width) + max_width
}

fn res_right_selected_prod_a_base(max_width: usize) -> usize {
    res_right_source_prod_b_base(max_width) + max_width
}

fn res_right_selected_prod_b_base(max_width: usize) -> usize {
    res_right_selected_prod_a_base(max_width) + max_width
}

fn split_u32_to_limbs(value: u32) -> [u32; RES_RANGE_LIMBS] {
    [
        value & (RES_RANGE_LIMB_BASE - 1),
        value >> RES_RANGE_LIMB_BITS,
    ]
}

fn limbs_to_expr<AB: AirBuilder>(limbs: &[AB::Var]) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing + Send + Sync,
{
    limbs
        .iter()
        .enumerate()
        .fold(AB::Expr::ZERO, |acc, (limb_index, limb)| {
            acc + AB::Expr::from(*limb)
                * AB::F::from_u64((RES_RANGE_LIMB_BASE as u64).pow(limb_index as u32))
        })
}

fn constrain_resolution_literal_zero<AB: AirBuilder>(
    builder: &mut AB,
    lit: AB::Var,
    is_zero: AB::Var,
    inv: AB::Var,
) where
    AB::F: PrimeCharacteristicRing + Send + Sync,
{
    let one = AB::Expr::ONE;
    builder.assert_bool(is_zero);

    let lit_expr: AB::Expr = lit.into();
    let is_zero_expr: AB::Expr = is_zero.into();
    let inv_expr: AB::Expr = inv.into();

    builder.assert_zero(is_zero_expr.clone() * lit_expr.clone());
    builder.assert_zero(
        (one.clone() - is_zero_expr.clone()) * (lit_expr.clone() * inv_expr - one.clone()),
    );
}

fn write_literal_zero_witness<F: Field + PrimeCharacteristicRing>(
    values: &mut [F],
    row_base: usize,
    aux_base: usize,
    lit: i32,
) {
    let is_zero = lit == 0;
    values[row_base + aux_base] = F::from_bool(is_zero);
    values[row_base + aux_base + 1] = if is_zero {
        F::ZERO
    } else {
        encode_signed_lit::<F>(lit).inverse()
    };
}

fn write_u32_limbs<F: Field + PrimeCharacteristicRing>(
    values: &mut [F],
    row_base: usize,
    limb_base: usize,
    value: u32,
) {
    for (limb_index, limb) in split_u32_to_limbs(value).into_iter().enumerate() {
        values[row_base + limb_base + limb_index] = F::from_u64(limb as u64);
    }
}

fn record_range_query(counts: &mut [u32], value: u32) {
    for limb in split_u32_to_limbs(value) {
        let slot = limb as usize;
        if let Some(count) = counts.get_mut(slot) {
            *count = count.saturating_add(1);
        }
    }
}

fn write_resolution_semantic_witness<F: Field + PrimeCharacteristicRing>(
    values: &mut [F],
    row_base: usize,
    max_width: usize,
    pivot_var: u32,
    resolvent: &[i32],
    left_clause: &[i32],
    right_clause: &[i32],
) {
    let pivot_lit = pivot_var as i32;
    let neg_pivot_lit = -pivot_lit;
    let pivot_field = F::from_u64(pivot_var as u64);
    let gamma_a = F::from_u64(RES_FP_GAMMA_A as u64);
    let gamma_b = F::from_u64(RES_FP_GAMMA_B as u64);

    let mut left_keep_flags = vec![false; max_width];
    let mut right_keep_flags = vec![false; max_width];
    for slot in 0..max_width {
        let lit = resolvent.get(slot).copied().unwrap_or(0);
        if lit == 0 {
            continue;
        }
        left_keep_flags[slot] = left_clause.contains(&lit) && lit != pivot_lit;
        right_keep_flags[slot] = right_clause.contains(&lit) && lit != neg_pivot_lit;
    }

    let mut left_source_count = 0u64;
    let mut left_selected_count = 0u64;
    let mut right_source_count = 0u64;
    let mut right_selected_count = 0u64;
    let mut left_source_prod_a = F::ONE;
    let mut left_source_prod_b = F::ONE;
    let mut left_selected_prod_a = F::ONE;
    let mut left_selected_prod_b = F::ONE;
    let mut right_source_prod_a = F::ONE;
    let mut right_source_prod_b = F::ONE;
    let mut right_selected_prod_a = F::ONE;
    let mut right_selected_prod_b = F::ONE;

    for slot in 0..max_width {
        let left_lit = left_clause.get(slot).copied().unwrap_or(0);
        let right_lit = right_clause.get(slot).copied().unwrap_or(0);
        let res_lit = resolvent.get(slot).copied().unwrap_or(0);

        let left_encoded = encode_signed_lit::<F>(left_lit);
        let right_encoded = encode_signed_lit::<F>(right_lit);
        let res_encoded = encode_signed_lit::<F>(res_lit);

        let left_pivot_flag = left_lit == pivot_lit;
        let right_neg_pivot_flag = right_lit == neg_pivot_lit;
        let left_diff = left_encoded - pivot_field;
        let right_diff = right_encoded + pivot_field;

        values[row_base + res_left_pivot_eq_base(max_width) + slot] = F::from_bool(left_pivot_flag);
        values[row_base + res_left_pivot_inv_base(max_width) + slot] = if left_pivot_flag {
            F::ZERO
        } else if left_diff == F::ZERO {
            F::ZERO
        } else {
            left_diff.inverse()
        };
        values[row_base + res_right_neg_pivot_eq_base(max_width) + slot] =
            F::from_bool(right_neg_pivot_flag);
        values[row_base + res_right_neg_pivot_inv_base(max_width) + slot] = if right_neg_pivot_flag
        {
            F::ZERO
        } else if right_diff == F::ZERO {
            F::ZERO
        } else {
            right_diff.inverse()
        };
        values[row_base + res_left_keep_base(max_width) + slot] =
            F::from_bool(left_keep_flags[slot]);
        values[row_base + res_right_keep_base(max_width) + slot] =
            F::from_bool(right_keep_flags[slot]);

        let left_source_active = left_lit != 0 && left_lit != pivot_lit;
        let right_source_active = right_lit != 0 && right_lit != neg_pivot_lit;
        let left_selected = left_keep_flags[slot];
        let right_selected = right_keep_flags[slot];

        left_source_count += u64::from(left_source_active);
        left_selected_count += u64::from(left_selected);
        right_source_count += u64::from(right_source_active);
        right_selected_count += u64::from(right_selected);

        values[row_base + res_left_source_count_base(max_width) + slot] =
            F::from_u64(left_source_count);
        values[row_base + res_left_selected_count_base(max_width) + slot] =
            F::from_u64(left_selected_count);
        values[row_base + res_right_source_count_base(max_width) + slot] =
            F::from_u64(right_source_count);
        values[row_base + res_right_selected_count_base(max_width) + slot] =
            F::from_u64(right_selected_count);

        if left_source_active {
            left_source_prod_a *= gamma_a - left_encoded;
            left_source_prod_b *= gamma_b - left_encoded;
        }
        if left_selected {
            left_selected_prod_a *= gamma_a - res_encoded;
            left_selected_prod_b *= gamma_b - res_encoded;
        }
        if right_source_active {
            right_source_prod_a *= gamma_a - right_encoded;
            right_source_prod_b *= gamma_b - right_encoded;
        }
        if right_selected {
            right_selected_prod_a *= gamma_a - res_encoded;
            right_selected_prod_b *= gamma_b - res_encoded;
        }

        values[row_base + res_left_source_prod_a_base(max_width) + slot] = left_source_prod_a;
        values[row_base + res_left_source_prod_b_base(max_width) + slot] = left_source_prod_b;
        values[row_base + res_left_selected_prod_a_base(max_width) + slot] = left_selected_prod_a;
        values[row_base + res_left_selected_prod_b_base(max_width) + slot] = left_selected_prod_b;
        values[row_base + res_right_source_prod_a_base(max_width) + slot] = right_source_prod_a;
        values[row_base + res_right_source_prod_b_base(max_width) + slot] = right_source_prod_b;
        values[row_base + res_right_selected_prod_a_base(max_width) + slot] = right_selected_prod_a;
        values[row_base + res_right_selected_prod_b_base(max_width) + slot] = right_selected_prod_b;
    }

    for clause_block in 0..3 {
        for slot in 0..max_width {
            let lit = match clause_block {
                0 => resolvent.get(slot).copied().unwrap_or(0),
                1 => left_clause.get(slot).copied().unwrap_or(0),
                _ => right_clause.get(slot).copied().unwrap_or(0),
            };
            write_literal_zero_witness(
                values,
                row_base,
                res_literal_aux_base(max_width, clause_block, slot),
                lit,
            );
        }
    }
}

fn sat_rows(instance: &ValidatedSatInstance) -> Vec<SatPreprocessedRow> {
    let mut query_rows = Vec::new();
    let mut occurrence_var_ids = Vec::new();

    for clause in &instance.formula.clauses {
        for (slot, lit) in clause.iter().enumerate() {
            let is_first = slot == 0;
            let is_last = slot + 1 == clause.len();
            let var_id = lit.unsigned_abs();
            occurrence_var_ids.push(var_id);
            query_rows.push(SatPreprocessedRow {
                is_query: true,
                is_sorted: false,
                var_id,
                sign: *lit < 0,
                clause_start: is_first,
                clause_end: is_last,
                same_clause_next: !is_last,
                same_var_next: false,
                is_terminal: false,
            });
        }
    }

    let mut sorted_var_ids = occurrence_var_ids;
    sorted_var_ids.sort_unstable();
    let mut rows = query_rows;
    for index in 0..sorted_var_ids.len() {
        let var_id = sorted_var_ids[index];
        rows.push(SatPreprocessedRow {
            is_query: false,
            is_sorted: true,
            var_id,
            sign: false,
            clause_start: false,
            clause_end: false,
            same_clause_next: false,
            same_var_next: sorted_var_ids.get(index + 1).copied() == Some(var_id),
            is_terminal: false,
        });
    }

    rows.push(SatPreprocessedRow {
        is_query: false,
        is_sorted: false,
        var_id: 0,
        sign: false,
        clause_start: false,
        clause_end: false,
        same_clause_next: false,
        same_var_next: false,
        is_terminal: true,
    });

    rows
}

fn sat_trace_height(instance: &ValidatedSatInstance) -> usize {
    padded_height(sat_rows(instance).len().max(2))
}

fn sat_preprocessed_matrix<F: PrimeCharacteristicRing + Send + Sync>(
    rows: &[SatPreprocessedRow],
) -> RowMajorMatrix<F> {
    let height = padded_height(rows.len().max(2));
    let mut values = vec![F::ZERO; height * SAT_PREP_WIDTH];

    for (row_index, row) in rows.iter().enumerate() {
        let base = row_index * SAT_PREP_WIDTH;
        values[base] = F::from_bool(row.is_query);
        values[base + 1] = F::from_bool(row.is_sorted);
        values[base + 2] = F::from_u64(row.var_id as u64);
        values[base + 3] = F::from_bool(row.sign);
        values[base + 4] = F::from_bool(row.clause_start);
        values[base + 5] = F::from_bool(row.clause_end);
        values[base + 6] = F::from_bool(row.same_clause_next);
        values[base + 7] = F::from_bool(row.same_var_next);
        values[base + 8] = F::from_bool(row.is_terminal);
    }

    RowMajorMatrix::new(values, SAT_PREP_WIDTH)
}

fn sat_trace<F: Field + PrimeCharacteristicRing + Send + Sync>(
    instance: &ValidatedSatInstance,
    rows: &[SatPreprocessedRow],
) -> RowMajorMatrix<F> {
    let height = padded_height(rows.len().max(2));
    let mut values = vec![F::ZERO; height * SAT_MAIN_WIDTH];

    let mut query_values = Vec::new();
    let mut query_truths = Vec::new();
    let mut query_prefix = Vec::new();
    for (clause_idx, clause) in instance.formula.clauses.iter().enumerate() {
        let mut prefix = false;
        for (slot, lit) in clause.iter().enumerate() {
            let var_index = lit.unsigned_abs() as usize - 1;
            let value = instance.assignment[var_index];
            let truth = instance.clause_truth_rows[clause_idx][slot];
            prefix |= truth;
            query_values.push(value);
            query_truths.push(truth);
            query_prefix.push(prefix);
        }
    }

    let mut sorted_values = query_values
        .iter()
        .copied()
        .zip(
            rows.iter()
                .filter(|row| row.is_query)
                .map(|row| row.var_id)
                .collect::<Vec<_>>(),
        )
        .map(|(value, var_id)| (var_id, value))
        .collect::<Vec<_>>();
    sorted_values.sort_unstable_by_key(|(var_id, _)| *var_id);

    let query_len = query_values.len();
    let sorted_offset = query_len;

    for index in 0..query_len {
        let base = index * SAT_MAIN_WIDTH;
        values[base + SAT_VALUE_COL] = F::from_bool(query_values[index]);
        values[base + SAT_TRUTH_COL] = F::from_bool(query_truths[index]);
        values[base + SAT_PREFIX_OR_COL] = F::from_bool(query_prefix[index]);
    }

    for (index, (_, value)) in sorted_values.iter().enumerate() {
        let base = (sorted_offset + index) * SAT_MAIN_WIDTH;
        values[base + SAT_VALUE_COL] = F::from_bool(*value);
    }

    let alpha = F::from_u64(SAT_PERM_ALPHA as u64);
    let beta = F::from_u64(SAT_PERM_BETA as u64);
    values[SAT_PRODUCT_COL] = F::ONE;
    for row_index in 0..height.saturating_sub(1) {
        let current = row_index * SAT_MAIN_WIDTH;
        let next = (row_index + 1) * SAT_MAIN_WIDTH;
        let row = rows.get(row_index);
        let (send_term, recv_term) = if let Some(row) = row {
            let fingerprint =
                alpha + F::from_u64(row.var_id as u64) + beta * values[current + SAT_VALUE_COL];
            let send = if row.is_query { fingerprint } else { F::ONE };
            let recv = if row.is_sorted { fingerprint } else { F::ONE };
            (send, recv)
        } else {
            (F::ONE, F::ONE)
        };
        values[next + SAT_PRODUCT_COL] = values[current + SAT_PRODUCT_COL] * send_term / recv_term;
    }

    RowMajorMatrix::new(values, SAT_MAIN_WIDTH)
}

fn resolution_lookup_preprocessed_matrix<F: PrimeCharacteristicRing + Send + Sync>(
    formula: &crate::backend::cnf::CnfFormula,
    max_width: usize,
    height: usize,
) -> RowMajorMatrix<F> {
    let width = max_width + 4;
    let mut values = vec![F::ZERO; height * width];

    for row_index in 0..height.min(RES_RANGE_TABLE_SIZE) {
        let base = row_index * width;
        values[base + res_lookup_prep_range_active_col(max_width)] = F::ONE;
        values[base + res_lookup_prep_range_value_col(max_width)] = F::from_u64(row_index as u64);
    }

    for (row_index, clause) in formula.clauses.iter().enumerate() {
        let base = row_index * width;
        values[base + RES_LOOKUP_PREP_FORMULA_ACTIVE_COL] = F::ONE;
        values[base + RES_LOOKUP_PREP_FORMULA_ID_COL] = F::from_u64((row_index + 1) as u64);
        for (slot, lit) in clause.iter().take(max_width).enumerate() {
            values[base + RES_LOOKUP_PREP_FORMULA_LIT_BASE + slot] = encode_signed_lit(*lit);
        }
    }

    RowMajorMatrix::new(values, width)
}

fn resolution_lookup_trace<F: Field + PrimeCharacteristicRing + Send + Sync>(
    instance: &ValidatedResolutionInstance,
    statement: &UnsatPublicStatement,
) -> RowMajorMatrix<F> {
    let max_width = statement.max_clause_width.max(1) as usize;
    let air_formula = normalize_resolution_air_formula(&statement.formula);
    let width = resolution_trace_width(max_width);
    let formula_rows = instance.formula.clauses.len();
    let step_count = instance
        .proof
        .steps
        .len()
        .max(instance.expanded_steps.len());
    let real_rows = formula_rows + step_count;
    let range_rows = resolution_range_table_rows(instance, statement);
    let height = padded_height((real_rows + 1).max(range_rows));
    let mut values = vec![F::ZERO; height * width];
    let mut parent_use_counts = vec![0u32; real_rows + 1];
    let mut range_use_counts = vec![0u32; RES_RANGE_TABLE_SIZE];

    for step in &instance.proof.steps {
        if let Some(count) = parent_use_counts.get_mut(step.left_parent as usize) {
            *count = count.saturating_add(1);
        }
        if let Some(count) = parent_use_counts.get_mut(step.right_parent as usize) {
            *count = count.saturating_add(1);
        }
    }

    for row_index in 0..height {
        let base = row_index * width;
        for clause_block in 0..3 {
            for slot in 0..max_width {
                write_literal_zero_witness(
                    &mut values,
                    base,
                    res_literal_aux_base(max_width, clause_block, slot),
                    0,
                );
            }
        }
    }

    let mut commit_acc_a = F::ZERO;
    let mut commit_acc_b = F::ZERO;
    let commit_width = instance.commitment.max_clause_width as usize;

    for (row_index, clause) in air_formula.clauses.iter().enumerate() {
        let base = row_index * width;
        values[base + RES_COMMIT_ACC_A_COL] = commit_acc_a;
        values[base + RES_COMMIT_ACC_B_COL] = commit_acc_b;
        values[base + RES_IS_SEMANTIC_COL] = F::ONE;
        values[base + RES_ENTRY_ID_COL] = F::from_u64((row_index + 1) as u64);
        values[base + RES_CLAUSE_MULT_COL] = F::from_u64(parent_use_counts[row_index + 1] as u64);
        for (slot, lit) in clause.iter().take(max_width).enumerate() {
            values[base + RES_HEADER_WIDTH + slot] = encode_signed_lit(*lit);
            write_literal_zero_witness(
                &mut values,
                base,
                res_literal_aux_base(max_width, 0, slot),
                *lit,
            );
        }
        let (clause_mix_a, clause_mix_b) =
            formula_clause_commitment_mix::<F>((row_index + 1) as u64, clause, commit_width);
        commit_acc_a = commit_acc_a * F::from_u64(COMMIT_ROOT_ALPHA_A) + clause_mix_a;
        commit_acc_b = commit_acc_b * F::from_u64(COMMIT_ROOT_ALPHA_B) + clause_mix_b;
    }

    if formula_rows < height {
        let base = formula_rows * width;
        values[base + RES_COMMIT_ACC_A_COL] = commit_acc_a;
        values[base + RES_COMMIT_ACC_B_COL] = commit_acc_b;
    }

    for step_index in 0..step_count {
        let row_index = formula_rows + step_index;
        let base = row_index * width;
        let proof_step = instance.proof.steps.get(step_index);
        let expanded_step = instance.expanded_steps.get(step_index);

        let pivot_var = proof_step
            .map(|step| step.pivot_var)
            .or_else(|| expanded_step.map(|step| step.pivot_var))
            .unwrap_or(0);
        let left_parent = proof_step.map(|step| step.left_parent).unwrap_or(0);
        let right_parent = proof_step.map(|step| step.right_parent).unwrap_or(0);
        let clause_id = (formula_rows + step_index + 1) as u32;

        let clause = expanded_step
            .map(|step| step.resolvent.as_slice())
            .unwrap_or(&[]);
        let clause = normalize_resolution_air_clause(clause);
        let left_clause = expanded_step
            .map(|step| step.left_clause.as_slice())
            .unwrap_or(&[]);
        let left_clause = normalize_resolution_air_clause(left_clause);
        let right_clause = expanded_step
            .map(|step| step.right_clause.as_slice())
            .unwrap_or(&[]);
        let right_clause = normalize_resolution_air_clause(right_clause);

        values[base + RES_IS_SEMANTIC_COL] = F::ONE;
        values[base + RES_IS_DERIVED_COL] = F::ONE;
        values[base + RES_ENTRY_ID_COL] = F::from_u64(clause_id as u64);
        values[base + RES_CLAUSE_MULT_COL] =
            F::from_u64(parent_use_counts[clause_id as usize] as u64);
        values[base + RES_LEFT_ID_COL] = F::from_u64(left_parent as u64);
        values[base + RES_RIGHT_ID_COL] = F::from_u64(right_parent as u64);
        values[base + RES_PIVOT_COL] = F::from_u64(pivot_var as u64);
        values[base + RES_PIVOT_INV_COL] = if pivot_var == 0 {
            F::ZERO
        } else {
            F::from_u64(pivot_var as u64).inverse()
        };
        values[base + RES_LEFT_ID_INV_COL] = if left_parent == 0 {
            F::ZERO
        } else {
            F::from_u64(left_parent as u64).inverse()
        };
        values[base + RES_RIGHT_ID_INV_COL] = if right_parent == 0 {
            F::ZERO
        } else {
            F::from_u64(right_parent as u64).inverse()
        };

        let left_gap = clause_id.saturating_sub(left_parent);
        let right_gap = clause_id.saturating_sub(right_parent);
        values[base + RES_LEFT_GAP_INV_COL] = if left_gap == 0 {
            F::ZERO
        } else {
            F::from_u64(left_gap as u64).inverse()
        };
        values[base + RES_RIGHT_GAP_INV_COL] = if right_gap == 0 {
            F::ZERO
        } else {
            F::from_u64(right_gap as u64).inverse()
        };

        write_u32_limbs(
            &mut values,
            base,
            res_pivot_delta_base(max_width),
            statement.num_vars.saturating_sub(pivot_var),
        );
        write_u32_limbs(&mut values, base, res_left_gap_base(max_width), left_gap);
        write_u32_limbs(&mut values, base, res_right_gap_base(max_width), right_gap);
        record_range_query(
            &mut range_use_counts,
            statement.num_vars.saturating_sub(pivot_var),
        );
        record_range_query(&mut range_use_counts, left_gap);
        record_range_query(&mut range_use_counts, right_gap);

        for (slot, lit) in clause.iter().take(max_width).enumerate() {
            values[base + RES_HEADER_WIDTH + slot] = encode_signed_lit(*lit);
            write_literal_zero_witness(
                &mut values,
                base,
                res_literal_aux_base(max_width, 0, slot),
                *lit,
            );
        }
        for (slot, lit) in left_clause.iter().take(max_width).enumerate() {
            values[base + RES_HEADER_WIDTH + max_width + slot] = encode_signed_lit(*lit);
            write_literal_zero_witness(
                &mut values,
                base,
                res_literal_aux_base(max_width, 1, slot),
                *lit,
            );
        }
        for (slot, lit) in right_clause.iter().take(max_width).enumerate() {
            values[base + RES_HEADER_WIDTH + max_width * 2 + slot] = encode_signed_lit(*lit);
            write_literal_zero_witness(
                &mut values,
                base,
                res_literal_aux_base(max_width, 2, slot),
                *lit,
            );
        }

        write_resolution_semantic_witness(
            &mut values,
            base,
            max_width,
            pivot_var,
            &clause,
            &left_clause,
            &right_clause,
        );
    }

    for (row_index, count) in range_use_counts.into_iter().enumerate() {
        if row_index >= height {
            break;
        }
        values[row_index * width + RES_IS_TABLE_COL] = F::from_u64(count as u64);
    }

    RowMajorMatrix::new(values, width)
}

fn formula_clause_commitment_mix<F: PrimeCharacteristicRing>(
    clause_index: u64,
    clause: &[i32],
    commitment_width: usize,
) -> (F, F) {
    let mut mix_a = F::from_u64(clause_index) * F::from_u64(COMMIT_INDEX_SCALE_A)
        + F::from_u64(clause.len() as u64) * F::from_u64(COMMIT_LEN_SCALE_A);
    let mut mix_b = F::from_u64(clause_index) * F::from_u64(COMMIT_INDEX_SCALE_B)
        + F::from_u64(clause.len() as u64) * F::from_u64(COMMIT_LEN_SCALE_B);

    for position in 0..commitment_width {
        let lit = clause.get(position).copied().unwrap_or(0);
        let lit_value = F::from_u64(commitment_literal_value(lit));
        mix_a += lit_value.clone() * F::from_u64((position as u64 + 1) * COMMIT_SLOT_SCALE_A);
        mix_b += lit_value * F::from_u64((position as u64 + 1) * COMMIT_SLOT_SCALE_B);
    }

    (mix_a, mix_b)
}

fn encode_signed_lit<F: PrimeCharacteristicRing>(lit: i32) -> F {
    if lit == 0 {
        return F::ZERO;
    }
    if lit > 0 {
        F::from_u64(lit as u64)
    } else {
        -F::from_u64((-lit) as u64)
    }
}

fn padded_height(n: usize) -> usize {
    n.next_power_of_two().max(1)
}

fn make_config() -> MyConfig {
    let mut rng = StdRng::seed_from_u64(7);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = Hash::new(perm.clone());
    let compress = Compress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = FriParameters {
        log_blowup: plonky3_env_usize("ZK_PROVER_FRI_LOG_BLOWUP", FRI_LOG_BLOWUP),
        log_final_poly_len: 0,
        max_log_arity: FRI_MAX_LOG_ARITY,
        num_queries: plonky3_env_usize("ZK_PROVER_FRI_NUM_QUERIES", FRI_NUM_QUERIES),
        commit_proof_of_work_bits: FRI_COMMIT_POW_BITS,
        query_proof_of_work_bits: FRI_QUERY_POW_BITS,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(dft, val_mmcs, fri_params);
    let challenger = Challenger::new(perm);
    MyConfig::new(pcs, challenger)
}

fn plonky3_env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|raw| raw.parse::<usize>().ok())
        .unwrap_or(default)
}

fn resolution_range_table_rows(
    instance: &ValidatedResolutionInstance,
    statement: &UnsatPublicStatement,
) -> usize {
    let formula_rows = instance.formula.clauses.len();
    let step_count = instance
        .proof
        .steps
        .len()
        .max(instance.expanded_steps.len());
    let mut max_limb = 0u32;

    let mut observe = |value: u32| {
        for limb in split_u32_to_limbs(value) {
            max_limb = max_limb.max(limb);
        }
    };

    for step_index in 0..step_count {
        let proof_step = instance.proof.steps.get(step_index);
        let pivot_var = proof_step
            .map(|step| step.pivot_var)
            .or_else(|| {
                instance
                    .expanded_steps
                    .get(step_index)
                    .map(|step| step.pivot_var)
            })
            .unwrap_or(0);
        let left_parent = proof_step.map(|step| step.left_parent).unwrap_or(0);
        let right_parent = proof_step.map(|step| step.right_parent).unwrap_or(0);
        let clause_id = (formula_rows + step_index + 1) as u32;

        observe(statement.num_vars.saturating_sub(pivot_var));
        observe(clause_id.saturating_sub(left_parent));
        observe(clause_id.saturating_sub(right_parent));
    }

    (max_limb as usize + 1).min(RES_RANGE_TABLE_SIZE).max(1)
}

#[cfg(test)]
mod tests {
    use crate::backend::cnf::CnfFormula;
    use crate::backend::phase2::{
        generate_resolution_proof_by_closure, validate_resolution_instance, validate_sat_instance,
        ExpandedResolutionStep, FormulaCommitment, ResolutionProof, ResolutionStep,
        ValidatedResolutionInstance,
    };

    use p3_air::symbolic::get_max_constraint_degree_extension;
    use p3_batch_stark::symbolic as batch_symbolic;
    use p3_lookup::logup::LogUpGadget;
    use p3_lookup::lookup_traits::LookupGadget;

    use super::*;

    fn sat_symbolic_layout() -> AirLayout {
        AirLayout {
            preprocessed_width: SAT_PREP_WIDTH,
            main_width: SAT_MAIN_WIDTH,
            ..Default::default()
        }
    }

    fn resolution_symbolic_layout(max_width: usize) -> AirLayout {
        AirLayout {
            preprocessed_width: max_width + 4,
            main_width: resolution_trace_width(max_width),
            num_public_values: UNSAT_PUBLIC_VALUES,
            ..Default::default()
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

    #[test]
    fn max_constraint_degree_hints_match_symbolic_evaluation() {
        let sat = SatAir { rows: Vec::new() };
        let sat_degree =
            get_max_constraint_degree_extension::<Val, Challenge, _>(&sat, sat_symbolic_layout());
        assert_eq!(sat_degree, SAT_MAX_CONSTRAINT_DEGREE);

        let formula = CnfFormula {
            num_vars: 2,
            clauses: vec![vec![1, 2], vec![-1]],
        };
        let statement = UnsatPublicStatement {
            formula,
            num_vars: 2,
            num_clauses: 2,
            max_clause_width: 2,
        };
        let max_width = statement.max_clause_width as usize;
        let mut resolution = resolution_lookup_air(&statement, 8);
        let lookups = resolution.get_lookups();
        let resolution_core_degree = get_max_constraint_degree_extension::<Val, Challenge, _>(
            &resolution,
            resolution_symbolic_layout(max_width),
        );
        assert_eq!(resolution_core_degree, 6);

        let lookup_gadget = LogUpGadget::new();
        let lookup_degree = lookups
            .iter()
            .map(|lookup| lookup_gadget.constraint_degree(lookup))
            .max()
            .unwrap_or(0);
        assert_eq!(lookup_degree, 8);

        let resolution_degree =
            batch_symbolic::get_max_constraint_degree::<Val, Challenge, _, LogUpGadget>(
                &resolution,
                resolution_symbolic_layout(max_width),
                &lookups,
                &lookup_gadget,
            );
        assert_eq!(resolution_degree, RESOLUTION_MAX_CONSTRAINT_DEGREE);
    }

    #[test]
    fn proves_sat_assignment_rows() {
        let formula = CnfFormula {
            num_vars: 2,
            clauses: vec![vec![1, -2], vec![2]],
        };
        let instance = validate_sat_instance(&formula, &[true, true]).unwrap();
        let proof = prove_sat(&instance).unwrap();
        verify_sat(&instance, &proof).unwrap();
    }

    #[test]
    fn proves_resolution_rows() {
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
    fn proves_resolution_rows_with_private_formula_commitment() {
        let formula = CnfFormula {
            num_vars: 1,
            clauses: vec![vec![1], vec![-1]],
        };
        let proof = generate_resolution_proof_by_closure(&formula, 8).unwrap();
        let instance = validate_resolution_instance(&formula, proof).unwrap();
        let proof = prove_unsat_committed(&instance).unwrap();
        verify_unsat_committed(&instance.committed_public_statement(), &proof).unwrap();
    }

    #[test]
    fn rejects_tampered_committed_formula_root_at_verification() {
        let formula = CnfFormula {
            num_vars: 1,
            clauses: vec![vec![1], vec![-1]],
        };
        let proof = generate_resolution_proof_by_closure(&formula, 8).unwrap();
        let instance = validate_resolution_instance(&formula, proof).unwrap();
        let proof = prove_unsat_committed(&instance).unwrap();
        let mut statement = instance.committed_public_statement();
        statement.commitment.mix_a = statement.commitment.mix_a.wrapping_add(1);

        assert!(matches!(
            verify_unsat_committed(&statement, &proof),
            Err(Plonky3BackendError::Verification(_))
        ));
    }

    #[test]
    fn proves_multi_step_resolution_rows() {
        let instance = synthetic_resolution_instance(2);
        let proof = prove_unsat(&instance).unwrap();
        verify_unsat(&instance.public_statement(), &proof).unwrap();
    }

    #[test]
    fn proves_resolution_with_duplicate_non_pivot_literals() {
        let formula = CnfFormula {
            num_vars: 2,
            clauses: vec![vec![1, 1, 2], vec![-2], vec![-1]],
        };
        let instance = validate_resolution_instance(
            &formula,
            ResolutionProof {
                steps: vec![
                    ResolutionStep {
                        left_parent: 1,
                        right_parent: 2,
                        pivot_var: 2,
                        resolvent: vec![1],
                    },
                    ResolutionStep {
                        left_parent: 4,
                        right_parent: 3,
                        pivot_var: 1,
                        resolvent: vec![],
                    },
                ],
            },
        )
        .unwrap();

        let proof = prove_unsat(&instance).unwrap();
        verify_unsat(&instance.public_statement(), &proof).unwrap();
    }

    #[test]
    fn rejects_tampered_public_formula_at_verification() {
        let instance = synthetic_resolution_instance(2);
        let proof = prove_unsat(&instance).unwrap();
        let mut statement = instance.public_statement();
        statement.formula.clauses[0][0] = -statement.formula.clauses[0][0];

        assert!(matches!(
            verify_unsat(&statement, &proof),
            Err(Plonky3BackendError::Verification(_))
        ));
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
            expanded_steps: vec![ExpandedResolutionStep {
                pivot_var: 0,
                left_clause: vec![0],
                right_clause: vec![0],
                resolvent: vec![0],
            }],
        };

        assert!(matches!(
            prove_unsat(&instance),
            Err(Plonky3BackendError::Verification(_))
        ));
    }

    #[test]
    fn rejects_parent_clause_not_present_in_known_set() {
        let formula = CnfFormula {
            num_vars: 1,
            clauses: vec![vec![1]],
        };
        let instance = ValidatedResolutionInstance {
            commitment: FormulaCommitment::from_formula(&formula).unwrap(),
            formula,
            proof: ResolutionProof {
                steps: vec![ResolutionStep {
                    left_parent: 1,
                    right_parent: 1,
                    pivot_var: 1,
                    resolvent: vec![],
                }],
            },
            expanded_steps: vec![ExpandedResolutionStep {
                pivot_var: 1,
                left_clause: vec![1],
                right_clause: vec![-1],
                resolvent: vec![],
            }],
        };

        assert!(matches!(
            prove_unsat(&instance),
            Err(Plonky3BackendError::Verification(_))
        ));
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
            expanded_steps: vec![ExpandedResolutionStep {
                pivot_var: 1,
                left_clause: vec![1, 2],
                right_clause: vec![-1],
                resolvent: vec![],
            }],
        };

        assert!(matches!(
            prove_unsat(&instance),
            Err(Plonky3BackendError::Verification(_))
        ));
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

        assert!(matches!(
            prove_unsat(&instance),
            Err(Plonky3BackendError::Verification(_))
        ));
    }

    #[test]
    fn accepts_unused_out_of_range_formula_literals() {
        let formula = CnfFormula {
            num_vars: 1,
            clauses: vec![vec![1], vec![-1], vec![2]],
        };
        let instance = validate_resolution_instance(
            &formula,
            ResolutionProof {
                steps: vec![ResolutionStep {
                    left_parent: 1,
                    right_parent: 2,
                    pivot_var: 1,
                    resolvent: vec![],
                }],
            },
        )
        .unwrap();

        let proof = prove_unsat(&instance).unwrap();
        verify_unsat(&instance.public_statement(), &proof).unwrap();
    }
}
