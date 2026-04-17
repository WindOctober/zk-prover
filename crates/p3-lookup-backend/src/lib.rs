use std::collections::BTreeMap;

use p3_air::symbolic::{AirLayout, SymbolicAirBuilder};
use p3_air::{Air, AirBuilder, BaseAir, BaseLeaf, SymbolicExpression, WindowAccess};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_batch_stark::{
    prove_batch, verify_batch, BatchProof, ProverData, StarkInstance, VerificationError,
};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_fri::{create_test_fri_params, TwoAdicFriPcs};
use p3_lookup::lookup_traits::{Direction, Kind, Lookup};
use p3_lookup::LookupAir;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;
use rand::{rngs::StdRng, SeedableRng};

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

const ACTIVE_COL_OFFSET: usize = 1;
const INTERACTION_TRACE_WIDTH: usize = 1;
const LOOKUP_BUS_NAME: &str = "subset_lookup_bus";

pub mod symbolic {
    use p3_air::SymbolicExpression;
    use p3_field::PrimeField32;
    use p3_lookup::lookup_traits::{Direction, Kind, Lookup};
    use p3_lookup::LookupAir;

    #[derive(Clone)]
    pub struct SymbolicInteraction<F> {
        pub values: Vec<SymbolicExpression<F>>,
        pub multiplicity: SymbolicExpression<F>,
        pub direction: Direction,
    }

    pub fn register_send_receive_bus<F, A>(
        air: &mut A,
        bus: impl Into<String>,
        interactions: &[SymbolicInteraction<F>],
    ) -> Lookup<F>
    where
        F: PrimeField32,
        A: LookupAir<F>,
    {
        let inputs = interactions
            .iter()
            .map(|interaction| {
                (
                    interaction.values.clone(),
                    interaction.multiplicity.clone(),
                    interaction.direction,
                )
            })
            .collect::<Vec<_>>();
        LookupAir::register_lookup(air, Kind::Global(bus.into()), &inputs)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AffineExpr {
    constant: i64,
    terms: Vec<(usize, i64)>,
}

impl AffineExpr {
    #[must_use]
    pub fn zero() -> Self {
        Self {
            constant: 0,
            terms: Vec::new(),
        }
    }

    #[must_use]
    pub fn constant(value: i64) -> Self {
        Self {
            constant: value,
            terms: Vec::new(),
        }
    }

    #[must_use]
    pub fn column(index: usize) -> Self {
        Self {
            constant: 0,
            terms: vec![(index, 1)],
        }
    }

    #[must_use]
    pub fn with_term(mut self, index: usize, coeff: i64) -> Self {
        self.terms.push((index, coeff));
        self
    }

    fn evaluate(&self, row: &[u32]) -> Result<u32, LookupBackendError> {
        let mut acc = field_from_i64(self.constant);
        for (index, coeff) in &self.terms {
            let value = row.get(*index).ok_or_else(|| {
                LookupBackendError::InvalidStatement(format!(
                    "expression referenced column {index}, but row width is {}",
                    row.len()
                ))
            })?;
            acc += field_from_i64(*coeff) * Val::from_u32(*value);
        }
        Ok(acc.as_canonical_u32())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TupleExpr {
    items: Vec<AffineExpr>,
}

impl TupleExpr {
    #[must_use]
    pub fn new(items: Vec<AffineExpr>) -> Self {
        Self { items }
    }

    #[must_use]
    pub fn single(expr: AffineExpr) -> Self {
        Self { items: vec![expr] }
    }

    #[must_use]
    pub fn arity(&self) -> usize {
        self.items.len()
    }

    fn evaluate(&self, row: &[u32]) -> Result<Vec<u32>, LookupBackendError> {
        self.items.iter().map(|expr| expr.evaluate(row)).collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WitnessMultiplicityKind {
    Unconstrained,
    Boolean,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InteractionMultiplicity {
    FixedOne,
    Witnessed { kind: WitnessMultiplicityKind },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InteractionSpec {
    pub bus: String,
    pub row_indices: Vec<usize>,
    pub tuple: TupleExpr,
    pub multiplicity: InteractionMultiplicity,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SendReceiveStatement {
    pub trace_width: usize,
    pub rows: Vec<Vec<u32>>,
    pub sends: Vec<InteractionSpec>,
    pub receives: Vec<InteractionSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SendReceiveWitness {
    pub sends: Vec<Option<Vec<u32>>>,
    pub receives: Vec<Option<Vec<u32>>>,
}

pub struct SendReceiveProof {
    pub proof: BatchProof<MyConfig>,
}

impl std::fmt::Debug for SendReceiveProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("SendReceiveProof(..)")
    }
}

pub type LookupProof = SendReceiveProof;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LookupConstraint {
    pub query_rows: Vec<usize>,
    pub table_rows: Vec<usize>,
    pub query_tuple: TupleExpr,
    pub table_tuple: TupleExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LookupInstance {
    pub trace_width: usize,
    pub rows: Vec<Vec<u32>>,
    pub constraint: LookupConstraint,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LookupTraceView {
    pub query_tuples: Vec<Vec<u32>>,
    pub table_tuples: Vec<Vec<u32>>,
    pub selected_table_rows: Vec<u32>,
}

#[derive(Debug, thiserror::Error)]
pub enum LookupBackendError {
    #[error("invalid send/receive statement: {0}")]
    InvalidStatement(String),
    #[error("invalid send/receive witness: {0}")]
    InvalidWitness(String),
    #[error("lookup relation is unsatisfied: {0}")]
    Unsatisfied(String),
    #[error("plonky3 verifier rejected the proof: {0}")]
    Verification(String),
}

#[derive(Clone)]
struct InteractionAir {
    bus: String,
    direction: Direction,
    row_width: usize,
    tuple: TupleExpr,
    multiplicity: InteractionMultiplicity,
    preprocessed: RowMajorMatrix<Val>,
    num_lookups: usize,
}

struct CompiledMaterial {
    airs: Vec<InteractionAir>,
    traces: Vec<RowMajorMatrix<Val>>,
    public_values: Vec<Vec<Val>>,
    degree_bits: Vec<usize>,
}

#[derive(Debug)]
struct EvaluatedLookup {
    query_tuples: Vec<Vec<u32>>,
    table_tuples: Vec<Vec<u32>>,
}

impl BaseAir<Val> for InteractionAir {
    fn width(&self) -> usize {
        INTERACTION_TRACE_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<Val>> {
        Some(self.preprocessed.clone())
    }
}

impl<AB: AirBuilder<F = Val>> Air<AB> for InteractionAir
where
    AB::F: PrimeField32,
{
    fn eval(&self, builder: &mut AB) {
        if let InteractionMultiplicity::Witnessed { kind } = self.multiplicity {
            let main = builder.main();
            let preprocessed = builder.preprocessed();
            let multiplicity = main.current(0).unwrap();
            let active = preprocessed.current(self.row_width).unwrap();

            builder.assert_zero(multiplicity.clone() * (AB::Expr::ONE - active));
            if matches!(kind, WitnessMultiplicityKind::Boolean) {
                builder.assert_bool(multiplicity);
            }
        }
    }
}

impl LookupAir<Val> for InteractionAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<Lookup<Val>> {
        self.num_lookups = 0;

        let symbolic_builder = SymbolicAirBuilder::<Val, Challenge>::new(AirLayout {
            preprocessed_width: self.preprocessed.width(),
            main_width: INTERACTION_TRACE_WIDTH,
            ..Default::default()
        });

        let preprocessed = symbolic_builder.preprocessed();
        let main = symbolic_builder.main();
        let prep_row = preprocessed.current_slice();
        let main_row = main.current_slice();

        let values = lower_tuple_expr(&self.tuple, prep_row);
        let multiplicity = match self.multiplicity {
            InteractionMultiplicity::FixedOne => prep_row[self.row_width].into(),
            InteractionMultiplicity::Witnessed { .. } => main_row[0].into(),
        };

        vec![LookupAir::register_lookup(
            self,
            Kind::Global(self.bus.clone()),
            &[(values, multiplicity, self.direction)],
        )]
    }
}

impl LookupInstance {
    pub fn trace_view(&self) -> Result<LookupTraceView, LookupBackendError> {
        let evaluated = evaluate_lookup_instance(self)?;
        let selected_table_rows =
            choose_subset_flags(&evaluated.table_tuples, &evaluated.query_tuples)?;
        Ok(LookupTraceView {
            query_tuples: evaluated.query_tuples,
            table_tuples: evaluated.table_tuples,
            selected_table_rows,
        })
    }
}

pub fn prove_send_receive(
    statement: &SendReceiveStatement,
    witness: &SendReceiveWitness,
) -> Result<SendReceiveProof, LookupBackendError> {
    let compiled = compile_send_receive(statement, Some(witness))?;
    let config = create_config();
    let mut airs = compiled.airs.clone();
    let prover_data = ProverData::from_airs_and_degrees(&config, &mut airs, &compiled.degree_bits);
    let common = &prover_data.common;
    let trace_refs = compiled.traces.iter().collect::<Vec<_>>();
    let instances =
        StarkInstance::new_multiple(&airs, &trace_refs, &compiled.public_values, common);
    let proof = prove_batch(&config, &instances, &prover_data);
    Ok(SendReceiveProof { proof })
}

pub fn verify_send_receive(
    statement: &SendReceiveStatement,
    proof: &SendReceiveProof,
) -> Result<(), LookupBackendError> {
    let compiled = compile_send_receive(statement, None)?;
    if compiled.degree_bits != proof.proof.degree_bits {
        return Err(LookupBackendError::Verification(format!(
            "proof degree bits {:?} do not match statement degree bits {:?}",
            proof.proof.degree_bits, compiled.degree_bits
        )));
    }

    let config = create_config();
    let mut airs = compiled.airs.clone();
    let prover_data = ProverData::from_airs_and_degrees(&config, &mut airs, &compiled.degree_bits);
    let common = &prover_data.common;

    verify_batch(
        &config,
        &airs,
        &proof.proof,
        &compiled.public_values,
        common,
    )
    .map_err(|err| LookupBackendError::Verification(render_verification_error(err)))
}

pub fn prove_lookup(instance: &LookupInstance) -> Result<LookupProof, LookupBackendError> {
    let evaluated = evaluate_lookup_instance(instance)?;
    let selected_table_rows =
        choose_subset_flags(&evaluated.table_tuples, &evaluated.query_tuples)?;
    let statement = compile_subset_statement(instance);
    let witness = SendReceiveWitness {
        sends: vec![Some(selected_table_rows)],
        receives: vec![None],
    };
    prove_send_receive(&statement, &witness)
}

pub fn verify_lookup(
    instance: &LookupInstance,
    proof: &LookupProof,
) -> Result<(), LookupBackendError> {
    let statement = compile_subset_statement(instance);
    verify_send_receive(&statement, proof)
}

fn compile_subset_statement(instance: &LookupInstance) -> SendReceiveStatement {
    SendReceiveStatement {
        trace_width: instance.trace_width,
        rows: instance.rows.clone(),
        sends: vec![InteractionSpec {
            bus: LOOKUP_BUS_NAME.to_owned(),
            row_indices: instance.constraint.table_rows.clone(),
            tuple: instance.constraint.table_tuple.clone(),
            multiplicity: InteractionMultiplicity::Witnessed {
                kind: WitnessMultiplicityKind::Boolean,
            },
        }],
        receives: vec![InteractionSpec {
            bus: LOOKUP_BUS_NAME.to_owned(),
            row_indices: instance.constraint.query_rows.clone(),
            tuple: instance.constraint.query_tuple.clone(),
            multiplicity: InteractionMultiplicity::FixedOne,
        }],
    }
}

fn compile_send_receive(
    statement: &SendReceiveStatement,
    witness: Option<&SendReceiveWitness>,
) -> Result<CompiledMaterial, LookupBackendError> {
    validate_statement(statement)?;
    if let Some(witness) = witness {
        validate_witness(statement, witness)?;
        check_send_receive_satisfaction(statement, witness)?;
    }

    let mut airs = Vec::with_capacity(statement.sends.len() + statement.receives.len());
    let mut traces = Vec::with_capacity(statement.sends.len() + statement.receives.len());
    let mut degree_bits = Vec::with_capacity(statement.sends.len() + statement.receives.len());

    for (idx, interaction) in statement.sends.iter().enumerate() {
        let witness_values = witness.and_then(|w| w.sends[idx].as_deref());
        let (air, trace, degree_bit) =
            compile_interaction(statement, interaction, Direction::Send, witness_values)?;
        airs.push(air);
        traces.push(trace);
        degree_bits.push(degree_bit);
    }

    for (idx, interaction) in statement.receives.iter().enumerate() {
        let witness_values = witness.and_then(|w| w.receives[idx].as_deref());
        let (air, trace, degree_bit) =
            compile_interaction(statement, interaction, Direction::Receive, witness_values)?;
        airs.push(air);
        traces.push(trace);
        degree_bits.push(degree_bit);
    }

    Ok(CompiledMaterial {
        airs,
        traces,
        public_values: vec![vec![]; degree_bits.len()],
        degree_bits,
    })
}

fn compile_interaction(
    statement: &SendReceiveStatement,
    interaction: &InteractionSpec,
    direction: Direction,
    witness_values: Option<&[u32]>,
) -> Result<(InteractionAir, RowMajorMatrix<Val>, usize), LookupBackendError> {
    let rows = extract_rows(&statement.rows, &interaction.row_indices)?;
    let height = padded_height(rows.len());
    let preprocessed = build_preprocessed_rows(&rows, statement.trace_width, height);
    let trace = build_main_trace(interaction, witness_values, height)?;
    let air = InteractionAir {
        bus: interaction.bus.clone(),
        direction,
        row_width: statement.trace_width,
        tuple: interaction.tuple.clone(),
        multiplicity: interaction.multiplicity.clone(),
        preprocessed,
        num_lookups: 0,
    };
    Ok((air, trace, height.ilog2() as usize))
}

fn validate_statement(statement: &SendReceiveStatement) -> Result<(), LookupBackendError> {
    if statement.trace_width == 0 {
        return Err(LookupBackendError::InvalidStatement(
            "trace width must be positive".to_owned(),
        ));
    }
    if statement.sends.is_empty() && statement.receives.is_empty() {
        return Err(LookupBackendError::InvalidStatement(
            "statement must contain at least one send or receive interaction".to_owned(),
        ));
    }

    for (row_index, row) in statement.rows.iter().enumerate() {
        if row.len() != statement.trace_width {
            return Err(LookupBackendError::InvalidStatement(format!(
                "row {row_index} has width {}, expected {}",
                row.len(),
                statement.trace_width
            )));
        }
        for (col_index, value) in row.iter().enumerate() {
            if *value >= Val::ORDER_U32 {
                return Err(LookupBackendError::InvalidStatement(format!(
                    "row {row_index} column {col_index} has value {value}, outside BabyBear field range",
                )));
            }
        }
    }

    let mut bus_arities = BTreeMap::<String, usize>::new();
    let mut bus_counts = BTreeMap::<String, (usize, usize)>::new();

    for interaction in statement.sends.iter().chain(statement.receives.iter()) {
        if interaction.bus.is_empty() {
            return Err(LookupBackendError::InvalidStatement(
                "interaction bus name must be non-empty".to_owned(),
            ));
        }
        if interaction.tuple.arity() == 0 {
            return Err(LookupBackendError::InvalidStatement(format!(
                "interaction on bus '{}' must have positive tuple arity",
                interaction.bus
            )));
        }
        for row_index in &interaction.row_indices {
            if *row_index >= statement.rows.len() {
                return Err(LookupBackendError::InvalidStatement(format!(
                    "row index {row_index} is out of bounds for {} rows",
                    statement.rows.len()
                )));
            }
        }

        match bus_arities.get(&interaction.bus) {
            Some(arity) if *arity != interaction.tuple.arity() => {
                return Err(LookupBackendError::InvalidStatement(format!(
                    "bus '{}' mixes tuple arities {} and {}",
                    interaction.bus,
                    arity,
                    interaction.tuple.arity()
                )));
            }
            None => {
                bus_arities.insert(interaction.bus.clone(), interaction.tuple.arity());
            }
            _ => {}
        }
    }

    for interaction in &statement.sends {
        let entry = bus_counts.entry(interaction.bus.clone()).or_default();
        entry.0 += 1;
    }
    for interaction in &statement.receives {
        let entry = bus_counts.entry(interaction.bus.clone()).or_default();
        entry.1 += 1;
    }
    for (bus, (send_count, receive_count)) in bus_counts {
        if send_count == 0 || receive_count == 0 {
            return Err(LookupBackendError::InvalidStatement(format!(
                "bus '{bus}' must have at least one send and one receive interaction",
            )));
        }
    }

    Ok(())
}

fn validate_witness(
    statement: &SendReceiveStatement,
    witness: &SendReceiveWitness,
) -> Result<(), LookupBackendError> {
    if witness.sends.len() != statement.sends.len() {
        return Err(LookupBackendError::InvalidWitness(format!(
            "send witness count {} does not match send interaction count {}",
            witness.sends.len(),
            statement.sends.len()
        )));
    }
    if witness.receives.len() != statement.receives.len() {
        return Err(LookupBackendError::InvalidWitness(format!(
            "receive witness count {} does not match receive interaction count {}",
            witness.receives.len(),
            statement.receives.len()
        )));
    }

    for (idx, interaction) in statement.sends.iter().enumerate() {
        validate_interaction_witness("send", idx, interaction, witness.sends[idx].as_deref())?;
    }
    for (idx, interaction) in statement.receives.iter().enumerate() {
        validate_interaction_witness(
            "receive",
            idx,
            interaction,
            witness.receives[idx].as_deref(),
        )?;
    }

    Ok(())
}

fn validate_interaction_witness(
    side: &str,
    index: usize,
    interaction: &InteractionSpec,
    witness_values: Option<&[u32]>,
) -> Result<(), LookupBackendError> {
    match interaction.multiplicity {
        InteractionMultiplicity::FixedOne => {
            if witness_values.is_some() {
                return Err(LookupBackendError::InvalidWitness(format!(
                    "{side} interaction {index} uses fixed multiplicity and must not provide witness values",
                )));
            }
        }
        InteractionMultiplicity::Witnessed { kind } => {
            let values = witness_values.ok_or_else(|| {
                LookupBackendError::InvalidWitness(format!(
                    "{side} interaction {index} requires witness multiplicities",
                ))
            })?;
            if values.len() != interaction.row_indices.len() {
                return Err(LookupBackendError::InvalidWitness(format!(
                    "{side} interaction {index} has {} witness multiplicities, expected {}",
                    values.len(),
                    interaction.row_indices.len()
                )));
            }
            for (row_idx, value) in values.iter().enumerate() {
                if *value >= Val::ORDER_U32 {
                    return Err(LookupBackendError::InvalidWitness(format!(
                        "{side} interaction {index} multiplicity at logical row {row_idx} has value {value}, outside BabyBear field range",
                    )));
                }
                if matches!(kind, WitnessMultiplicityKind::Boolean) && *value > 1 {
                    return Err(LookupBackendError::InvalidWitness(format!(
                        "{side} interaction {index} multiplicity at logical row {row_idx} must be boolean, got {value}",
                    )));
                }
            }
        }
    }

    Ok(())
}

fn check_send_receive_satisfaction(
    statement: &SendReceiveStatement,
    witness: &SendReceiveWitness,
) -> Result<(), LookupBackendError> {
    let mut bus_balances = BTreeMap::<String, BTreeMap<Vec<u32>, i128>>::new();

    for (idx, interaction) in statement.sends.iter().enumerate() {
        accumulate_interaction(
            &mut bus_balances,
            statement,
            interaction,
            witness.sends[idx].as_deref(),
            -1,
        )?;
    }
    for (idx, interaction) in statement.receives.iter().enumerate() {
        accumulate_interaction(
            &mut bus_balances,
            statement,
            interaction,
            witness.receives[idx].as_deref(),
            1,
        )?;
    }

    for (bus, balances) in bus_balances {
        if let Some((tuple, delta)) = balances.into_iter().find(|(_, delta)| *delta != 0) {
            return Err(LookupBackendError::Unsatisfied(format!(
                "bus '{bus}' is imbalanced on tuple {:?} with signed multiplicity {}",
                tuple, delta
            )));
        }
    }
    Ok(())
}

fn accumulate_interaction(
    bus_balances: &mut BTreeMap<String, BTreeMap<Vec<u32>, i128>>,
    statement: &SendReceiveStatement,
    interaction: &InteractionSpec,
    witness_values: Option<&[u32]>,
    sign: i128,
) -> Result<(), LookupBackendError> {
    let rows = extract_rows(&statement.rows, &interaction.row_indices)?;
    let tuples = rows
        .iter()
        .map(|row| interaction.tuple.evaluate(row))
        .collect::<Result<Vec<_>, _>>()?;
    let multiplicities = match interaction.multiplicity {
        InteractionMultiplicity::FixedOne => vec![1u32; tuples.len()],
        InteractionMultiplicity::Witnessed { .. } => witness_values.unwrap().to_vec(),
    };

    let bus_balance = bus_balances.entry(interaction.bus.clone()).or_default();
    for (tuple, multiplicity) in tuples.into_iter().zip(multiplicities) {
        *bus_balance.entry(tuple).or_default() += sign * i128::from(multiplicity);
    }
    Ok(())
}

fn build_main_trace(
    interaction: &InteractionSpec,
    witness_values: Option<&[u32]>,
    height: usize,
) -> Result<RowMajorMatrix<Val>, LookupBackendError> {
    let mut values = vec![Val::ZERO; height * INTERACTION_TRACE_WIDTH];
    if let InteractionMultiplicity::Witnessed { .. } = interaction.multiplicity {
        if let Some(witness_values) = witness_values {
            for (idx, value) in witness_values.iter().enumerate() {
                values[idx] = Val::from_u32(*value);
            }
        }
    }
    Ok(RowMajorMatrix::new(values, INTERACTION_TRACE_WIDTH))
}

fn extract_rows(
    rows: &[Vec<u32>],
    row_indices: &[usize],
) -> Result<Vec<Vec<u32>>, LookupBackendError> {
    row_indices
        .iter()
        .map(|row_index| {
            rows.get(*row_index).cloned().ok_or_else(|| {
                LookupBackendError::InvalidStatement(format!(
                    "row index {row_index} is out of bounds for {} rows",
                    rows.len()
                ))
            })
        })
        .collect()
}

fn build_preprocessed_rows(
    rows: &[Vec<u32>],
    row_width: usize,
    height: usize,
) -> RowMajorMatrix<Val> {
    let width = row_width + ACTIVE_COL_OFFSET;
    let mut values = vec![Val::ZERO; height * width];
    for (row_idx, row) in rows.iter().enumerate() {
        for (col_idx, value) in row.iter().enumerate() {
            values[row_idx * width + col_idx] = Val::from_u32(*value);
        }
        values[row_idx * width + row_width] = Val::ONE;
    }
    RowMajorMatrix::new(values, width)
}

fn lower_tuple_expr(
    tuple: &TupleExpr,
    row: &[p3_air::SymbolicVariable<Val>],
) -> Vec<SymbolicExpression<Val>> {
    tuple
        .items
        .iter()
        .map(|expr| lower_affine_expr(expr, row))
        .collect()
}

fn lower_affine_expr(
    expr: &AffineExpr,
    row: &[p3_air::SymbolicVariable<Val>],
) -> SymbolicExpression<Val> {
    let mut acc = SymbolicExpression::Leaf(BaseLeaf::Constant(field_from_i64(expr.constant)));
    for (index, coeff) in &expr.terms {
        acc = acc + SymbolicExpression::from(row[*index]) * field_from_i64(*coeff);
    }
    acc
}

fn evaluate_lookup_instance(
    instance: &LookupInstance,
) -> Result<EvaluatedLookup, LookupBackendError> {
    let statement = compile_subset_statement(instance);
    validate_statement(&statement)?;

    let query_rows = extract_rows(&instance.rows, &instance.constraint.query_rows)?;
    let table_rows = extract_rows(&instance.rows, &instance.constraint.table_rows)?;
    let query_tuples = query_rows
        .iter()
        .map(|row| instance.constraint.query_tuple.evaluate(row))
        .collect::<Result<Vec<_>, _>>()?;
    let table_tuples = table_rows
        .iter()
        .map(|row| instance.constraint.table_tuple.evaluate(row))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(EvaluatedLookup {
        query_tuples,
        table_tuples,
    })
}

fn choose_subset_flags(
    table_tuples: &[Vec<u32>],
    query_tuples: &[Vec<u32>],
) -> Result<Vec<u32>, LookupBackendError> {
    let mut outstanding = BTreeMap::<Vec<u32>, usize>::new();
    for tuple in query_tuples {
        *outstanding.entry(tuple.clone()).or_default() += 1;
    }

    let mut flags = Vec::with_capacity(table_tuples.len());
    for tuple in table_tuples {
        let take = if let Some(remaining) = outstanding.get_mut(tuple) {
            if *remaining > 0 {
                *remaining -= 1;
                true
            } else {
                false
            }
        } else {
            false
        };
        flags.push(u32::from(take));
    }

    if let Some((missing_tuple, remaining)) = outstanding
        .into_iter()
        .find(|(_, remaining)| *remaining > 0)
    {
        return Err(LookupBackendError::Unsatisfied(format!(
            "missing {remaining} occurrence(s) of query tuple {:?} in the table",
            missing_tuple
        )));
    }
    Ok(flags)
}

fn create_config() -> MyConfig {
    let perm = Perm::new_from_rng_128(&mut StdRng::seed_from_u64(0x5eed_u64));
    let hash = Hash::new(perm.clone());
    let compress = Compress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params(challenge_mmcs, 2);
    let pcs = Pcs::new(dft, val_mmcs, fri_params);
    let challenger = Challenger::new(perm);
    StarkConfig::new(pcs, challenger)
}

fn padded_height(logical_len: usize) -> usize {
    logical_len.max(16).next_power_of_two()
}

fn field_from_i64(value: i64) -> Val {
    if value >= 0 {
        Val::from_u64(value as u64)
    } else {
        -Val::from_u64(value.unsigned_abs())
    }
}

fn render_verification_error(err: VerificationError<impl std::fmt::Debug>) -> String {
    format!("{err:?}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proves_send_receive_with_private_selector() {
        let statement = SendReceiveStatement {
            trace_width: 2,
            rows: vec![vec![1, 10], vec![2, 20], vec![1, 30], vec![3, 40]],
            sends: vec![InteractionSpec {
                bus: "memory".to_owned(),
                row_indices: vec![0, 1, 2, 3],
                tuple: TupleExpr::single(AffineExpr::column(0)),
                multiplicity: InteractionMultiplicity::Witnessed {
                    kind: WitnessMultiplicityKind::Boolean,
                },
            }],
            receives: vec![InteractionSpec {
                bus: "memory".to_owned(),
                row_indices: vec![0, 2],
                tuple: TupleExpr::single(AffineExpr::column(0)),
                multiplicity: InteractionMultiplicity::FixedOne,
            }],
        };
        let witness = SendReceiveWitness {
            sends: vec![Some(vec![1, 0, 1, 0])],
            receives: vec![None],
        };

        let proof = prove_send_receive(&statement, &witness).expect("proof should succeed");
        verify_send_receive(&statement, &proof).expect("proof should verify");
    }

    #[test]
    fn rejects_invalid_private_selector_witness() {
        let statement = SendReceiveStatement {
            trace_width: 1,
            rows: vec![vec![1], vec![2], vec![3]],
            sends: vec![InteractionSpec {
                bus: "memory".to_owned(),
                row_indices: vec![0, 1, 2],
                tuple: TupleExpr::single(AffineExpr::column(0)),
                multiplicity: InteractionMultiplicity::Witnessed {
                    kind: WitnessMultiplicityKind::Boolean,
                },
            }],
            receives: vec![InteractionSpec {
                bus: "memory".to_owned(),
                row_indices: vec![0, 2],
                tuple: TupleExpr::single(AffineExpr::column(0)),
                multiplicity: InteractionMultiplicity::FixedOne,
            }],
        };
        let witness = SendReceiveWitness {
            sends: vec![Some(vec![0, 1, 0])],
            receives: vec![None],
        };

        let err = prove_send_receive(&statement, &witness)
            .expect_err("witness should not satisfy the lookup");
        assert!(matches!(err, LookupBackendError::Unsatisfied(_)));
    }

    #[test]
    fn proves_single_column_subset() {
        let instance = LookupInstance {
            trace_width: 2,
            rows: vec![vec![1, 10], vec![2, 20], vec![1, 30], vec![3, 40]],
            constraint: LookupConstraint {
                query_rows: vec![0, 2],
                table_rows: vec![0, 1, 2, 3],
                query_tuple: TupleExpr::single(AffineExpr::column(0)),
                table_tuple: TupleExpr::single(AffineExpr::column(0)),
            },
        };
        let proof = prove_lookup(&instance).expect("subset should be satisfiable");
        verify_lookup(&instance, &proof).expect("proof should verify");
    }

    #[test]
    fn proves_affine_tuple_subset() {
        let instance = LookupInstance {
            trace_width: 3,
            rows: vec![
                vec![2, 5, 9],
                vec![4, 3, 8],
                vec![7, 1, 4],
                vec![2, 5, 9],
                vec![9, 0, 2],
            ],
            constraint: LookupConstraint {
                query_rows: vec![0, 1],
                table_rows: vec![3, 4, 1, 2],
                query_tuple: TupleExpr::new(vec![
                    AffineExpr::column(0).with_term(1, 2),
                    AffineExpr::column(2).with_term(1, -1),
                ]),
                table_tuple: TupleExpr::new(vec![
                    AffineExpr::column(0).with_term(1, 2),
                    AffineExpr::column(2).with_term(1, -1),
                ]),
            },
        };
        let proof = prove_lookup(&instance).expect("subset should be satisfiable");
        verify_lookup(&instance, &proof).expect("proof should verify");
    }

    #[test]
    fn rejects_unsatisfied_subset() {
        let instance = LookupInstance {
            trace_width: 1,
            rows: vec![vec![1], vec![2], vec![3]],
            constraint: LookupConstraint {
                query_rows: vec![0, 2],
                table_rows: vec![1],
                query_tuple: TupleExpr::single(AffineExpr::column(0)),
                table_tuple: TupleExpr::single(AffineExpr::column(0)),
            },
        };
        let err = match prove_lookup(&instance) {
            Ok(_) => panic!("subset should be unsatisfied"),
            Err(err) => err,
        };
        assert!(matches!(err, LookupBackendError::Unsatisfied(_)));
    }

    #[test]
    fn rejects_tampered_instance_at_verification() {
        let instance = LookupInstance {
            trace_width: 2,
            rows: vec![vec![5, 1], vec![7, 2], vec![5, 3]],
            constraint: LookupConstraint {
                query_rows: vec![0, 2],
                table_rows: vec![0, 1, 2],
                query_tuple: TupleExpr::single(AffineExpr::column(0)),
                table_tuple: TupleExpr::single(AffineExpr::column(0)),
            },
        };
        let proof = prove_lookup(&instance).expect("original instance should prove");

        let mut tampered = instance.clone();
        tampered.rows[1][0] = 42;
        let err = verify_lookup(&tampered, &proof).expect_err("tampered instance must fail");
        assert!(matches!(err, LookupBackendError::Verification(_)));
    }
}
