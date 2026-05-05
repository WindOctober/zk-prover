use resolution_verifier_core::FlatResolutionWitness;
use serde::{Deserialize, Serialize};

use crate::backend::cnf::{CnfFormula, Lit};

pub(crate) const COMMIT_FIELD_MODULUS: u64 = 2_013_265_921;
pub(crate) const COMMIT_ROOT_ALPHA_A: u64 = 1_000_003;
pub(crate) const COMMIT_ROOT_ALPHA_B: u64 = 1_000_033;
pub(crate) const COMMIT_INDEX_SCALE_A: u64 = 104_729;
pub(crate) const COMMIT_INDEX_SCALE_B: u64 = 130_363;
pub(crate) const COMMIT_LEN_SCALE_A: u64 = 911_382_323;
pub(crate) const COMMIT_LEN_SCALE_B: u64 = 972_663_749;
pub(crate) const COMMIT_SLOT_SCALE_A: u64 = 65_537;
pub(crate) const COMMIT_SLOT_SCALE_B: u64 = 131_071;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FormulaCommitment {
    pub num_vars: u32,
    pub num_clauses: u32,
    pub max_clause_width: u32,
    pub mix_a: u32,
    pub mix_b: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolutionStep {
    pub left_parent: u32,
    pub right_parent: u32,
    pub pivot_var: u32,
    pub resolvent: Vec<Lit>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolutionProof {
    pub steps: Vec<ResolutionStep>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidatedSatInstance {
    pub formula: CnfFormula,
    pub commitment: FormulaCommitment,
    pub assignment: Vec<bool>,
    pub clause_truth_rows: Vec<Vec<bool>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpandedResolutionStep {
    pub pivot_var: u32,
    pub left_clause: Vec<Lit>,
    pub right_clause: Vec<Lit>,
    pub resolvent: Vec<Lit>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidatedResolutionInstance {
    pub formula: CnfFormula,
    pub commitment: FormulaCommitment,
    pub proof: ResolutionProof,
    pub expanded_steps: Vec<ExpandedResolutionStep>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnsatPublicStatement {
    pub formula: CnfFormula,
    pub num_vars: u32,
    pub num_clauses: u32,
    pub max_clause_width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommittedUnsatPublicStatement {
    pub commitment: FormulaCommitment,
    pub air_max_clause_width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatOutcome {
    Sat(ValidatedSatInstance),
    Unsat(ValidatedResolutionInstance),
}

#[derive(Debug, thiserror::Error)]
pub enum Phase2Error {
    #[error("assignment length {actual} does not match CNF variable count {expected}")]
    AssignmentLength { expected: usize, actual: usize },
    #[error("assignment does not satisfy clause #{clause_index}")]
    UnsatisfiedClause { clause_index: usize },
    #[error("resolution proof references an unknown clause id {0}")]
    UnknownClause(u32),
    #[error("resolution proof step {step} does not resolve on pivot x{pivot}")]
    MissingPivot { step: usize, pivot: u32 },
    #[error("resolution proof step {step} resolvent does not match the parents")]
    BadResolvent { step: usize },
    #[error("resolution proof does not derive the empty clause")]
    MissingEmptyClause,
    #[error("resolution closure did not derive the empty clause within {0} steps")]
    ResolutionLimit(usize),
    #[error("formula commitment overflowed the prototype commitment range")]
    CommitmentOverflow,
    #[error("external SAT solver reported UNSAT but no resolution derivation was found")]
    UnsatWithoutResolution,
}

#[derive(Debug, thiserror::Error)]
pub enum ExternalResolutionTraceError {
    #[error("malformed unfolded trace line {line}: {reason}")]
    MalformedLine { line: usize, reason: String },
    #[error("unfolded trace row {row} references unknown support row {support}")]
    UnknownSupport { row: usize, support: usize },
    #[error("unfolded trace row {row} has {actual} supports; expected 0 or 2")]
    UnsupportedArity { row: usize, actual: usize },
    #[error("unfolded trace row {row} is missing a pivot literal")]
    MissingPivot { row: usize },
    #[error(
        "unfolded trace row {row} references an initial clause not present in the source formula"
    )]
    UnknownInitialClause { row: usize },
    #[error("validated resolution instance rejected the external trace: {0}")]
    Validation(#[from] Phase2Error),
}

impl FormulaCommitment {
    pub fn from_formula(formula: &CnfFormula) -> Result<Self, Phase2Error> {
        let mut canonical_clauses = Vec::with_capacity(formula.clauses.len());
        let mut max_clause_width = 0usize;
        for clause in &formula.clauses {
            let mut normalized = clause.clone();
            normalized.sort_unstable();
            normalized.dedup();
            max_clause_width = max_clause_width.max(normalized.len());
            canonical_clauses.push(normalized);
        }

        let slot_weights_a = commitment_slot_weights(max_clause_width, COMMIT_SLOT_SCALE_A);
        let slot_weights_b = commitment_slot_weights(max_clause_width, COMMIT_SLOT_SCALE_B);

        let mut mix_a = 0u64;
        let mut mix_b = 0u64;

        for (index, clause) in canonical_clauses.iter().enumerate() {
            let clause_index = (index + 1) as u64;
            let (clause_mix_a, clause_mix_b) =
                clause_weight_pair(clause_index, clause, &slot_weights_a, &slot_weights_b);
            mix_a = field_add(field_mul(mix_a, COMMIT_ROOT_ALPHA_A), clause_mix_a);
            mix_b = field_add(field_mul(mix_b, COMMIT_ROOT_ALPHA_B), clause_mix_b);
        }

        Ok(Self {
            num_vars: formula.num_vars,
            num_clauses: formula.clauses.len() as u32,
            max_clause_width: max_clause_width as u32,
            mix_a: mix_a as u32,
            mix_b: mix_b as u32,
        })
    }
}

impl std::fmt::Display for FormulaCommitment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "v{}-c{}-w{}-{:#010x}-{:#010x}",
            self.num_vars, self.num_clauses, self.max_clause_width, self.mix_a, self.mix_b
        )
    }
}

impl UnsatPublicStatement {
    pub fn from_formula(formula: &CnfFormula) -> Result<Self, Phase2Error> {
        let commitment = FormulaCommitment::from_formula(formula)?;
        Ok(Self {
            formula: formula.clone(),
            num_vars: commitment.num_vars,
            num_clauses: commitment.num_clauses,
            max_clause_width: commitment.max_clause_width,
        })
    }

    pub fn from_commitment_and_formula(
        commitment: &FormulaCommitment,
        formula: &CnfFormula,
    ) -> Self {
        Self {
            formula: formula.clone(),
            num_vars: commitment.num_vars,
            num_clauses: commitment.num_clauses,
            max_clause_width: commitment.max_clause_width,
        }
    }
}

impl ValidatedResolutionInstance {
    pub fn max_resolution_clause_width(&self) -> u32 {
        let formula_max = self
            .formula
            .clauses
            .iter()
            .map(|clause| clause.len() as u32)
            .max()
            .unwrap_or(0);
        let proof_max = self
            .expanded_steps
            .iter()
            .flat_map(|step| {
                [
                    step.left_clause.len() as u32,
                    step.right_clause.len() as u32,
                    step.resolvent.len() as u32,
                ]
            })
            .max()
            .unwrap_or(0);
        formula_max.max(proof_max)
    }

    pub fn public_statement(&self) -> UnsatPublicStatement {
        UnsatPublicStatement {
            formula: self.formula.clone(),
            num_vars: self.commitment.num_vars,
            num_clauses: self.commitment.num_clauses,
            max_clause_width: self.max_resolution_clause_width(),
        }
    }

    pub fn committed_public_statement(&self) -> CommittedUnsatPublicStatement {
        CommittedUnsatPublicStatement {
            commitment: self.commitment.clone(),
            air_max_clause_width: self.max_resolution_clause_width(),
        }
    }

    pub fn flat_witness(&self) -> FlatResolutionWitness {
        let mut initial_clause_offsets = Vec::with_capacity(self.formula.clauses.len() + 1);
        let mut initial_clause_literals = Vec::new();
        initial_clause_offsets.push(0);
        for clause in &self.formula.clauses {
            initial_clause_literals.extend_from_slice(clause);
            initial_clause_offsets.push(initial_clause_literals.len() as u32);
        }

        let mut step_resolvent_offsets = Vec::with_capacity(self.proof.steps.len() + 1);
        let mut step_resolvent_literals = Vec::new();
        step_resolvent_offsets.push(0);
        for step in &self.expanded_steps {
            step_resolvent_literals.extend_from_slice(&step.resolvent);
            step_resolvent_offsets.push(step_resolvent_literals.len() as u32);
        }

        FlatResolutionWitness {
            num_vars: self.commitment.num_vars,
            initial_clause_offsets,
            initial_clause_literals,
            step_left_parents: self
                .proof
                .steps
                .iter()
                .map(|step| step.left_parent)
                .collect(),
            step_right_parents: self
                .proof
                .steps
                .iter()
                .map(|step| step.right_parent)
                .collect(),
            step_pivot_vars: self.proof.steps.iter().map(|step| step.pivot_var).collect(),
            step_resolvent_offsets,
            step_resolvent_literals,
        }
    }
}

pub fn validate_sat_instance(
    formula: &CnfFormula,
    assignment: &[bool],
) -> Result<ValidatedSatInstance, Phase2Error> {
    if assignment.len() != formula.num_vars as usize {
        return Err(Phase2Error::AssignmentLength {
            expected: formula.num_vars as usize,
            actual: assignment.len(),
        });
    }

    let commitment = FormulaCommitment::from_formula(formula)?;
    let mut clause_truth_rows = Vec::with_capacity(formula.clauses.len());

    for (clause_index, clause) in formula.clauses.iter().enumerate() {
        let mut truth_row = Vec::with_capacity(clause.len());
        let mut satisfied = false;
        for &lit in clause {
            let value = eval_lit(lit, assignment);
            truth_row.push(value);
            satisfied |= value;
        }
        if !satisfied {
            return Err(Phase2Error::UnsatisfiedClause { clause_index });
        }
        clause_truth_rows.push(truth_row);
    }

    Ok(ValidatedSatInstance {
        formula: formula.clone(),
        commitment,
        assignment: assignment.to_vec(),
        clause_truth_rows,
    })
}

pub fn validate_resolution_instance(
    formula: &CnfFormula,
    proof: ResolutionProof,
) -> Result<ValidatedResolutionInstance, Phase2Error> {
    let commitment = FormulaCommitment::from_formula(formula)?;
    let mut known = formula.clauses.clone();
    let mut expanded_steps = Vec::with_capacity(proof.steps.len());
    let mut validated_steps = Vec::with_capacity(proof.steps.len());

    for (step_index, step) in proof.steps.iter().enumerate() {
        let left = clause_by_id(&known, step.left_parent)?;
        let right = clause_by_id(&known, step.right_parent)?;
        let pivot = step.pivot_var as Lit;
        let resolvent = normalize_clause(&step.resolvent);

        if !left.contains(&pivot) || !right.contains(&-pivot) {
            return Err(Phase2Error::MissingPivot {
                step: step_index,
                pivot: step.pivot_var,
            });
        }

        let expected = resolve_clauses(&left, &right, step.pivot_var);
        if expected != resolvent {
            return Err(Phase2Error::BadResolvent { step: step_index });
        }

        known.push(resolvent.clone());
        validated_steps.push(ResolutionStep {
            left_parent: step.left_parent,
            right_parent: step.right_parent,
            pivot_var: step.pivot_var,
            resolvent: resolvent.clone(),
        });
        expanded_steps.push(ExpandedResolutionStep {
            pivot_var: step.pivot_var,
            left_clause: left,
            right_clause: right,
            resolvent,
        });
    }

    if known
        .last()
        .map(|clause| !clause.is_empty())
        .unwrap_or(true)
    {
        return Err(Phase2Error::MissingEmptyClause);
    }

    Ok(ValidatedResolutionInstance {
        formula: formula.clone(),
        commitment,
        proof: ResolutionProof {
            steps: validated_steps,
        },
        expanded_steps,
    })
}

pub fn validate_resolution_instance_from_unfolded_trace(
    formula: &CnfFormula,
    unfolded_trace: &str,
) -> Result<ValidatedResolutionInstance, ExternalResolutionTraceError> {
    let clause_ids = formula.clauses.iter().enumerate().fold(
        std::collections::BTreeMap::<Vec<Lit>, u32>::new(),
        |mut ids, (index, clause)| {
            ids.entry(normalize_clause(clause))
                .or_insert((index + 1) as u32);
            ids
        },
    );
    let parsed_rows = parse_unfolded_trace_rows(unfolded_trace)?;

    let mut row_to_clause_id = std::collections::BTreeMap::<usize, u32>::new();
    let mut row_to_clause = std::collections::BTreeMap::<usize, Vec<Lit>>::new();
    let mut steps = Vec::new();

    for row in parsed_rows {
        let clause = normalize_clause(&row.clause);

        if row.support.is_empty() {
            let clause_id = clause_ids
                .get(&clause)
                .copied()
                .ok_or(ExternalResolutionTraceError::UnknownInitialClause { row: row.index })?;
            row_to_clause_id.insert(row.index, clause_id);
            row_to_clause.insert(row.index, clause);
            continue;
        }

        if row.support.len() != 2 {
            return Err(ExternalResolutionTraceError::UnsupportedArity {
                row: row.index,
                actual: row.support.len(),
            });
        }

        let mut left_parent = row_to_clause_id.get(&row.support[0]).copied().ok_or(
            ExternalResolutionTraceError::UnknownSupport {
                row: row.index,
                support: row.support[0],
            },
        )?;
        let mut right_parent = row_to_clause_id.get(&row.support[1]).copied().ok_or(
            ExternalResolutionTraceError::UnknownSupport {
                row: row.index,
                support: row.support[1],
            },
        )?;
        let mut left_clause = row_to_clause.get(&row.support[0]).cloned().ok_or(
            ExternalResolutionTraceError::UnknownSupport {
                row: row.index,
                support: row.support[0],
            },
        )?;
        let mut right_clause = row_to_clause.get(&row.support[1]).cloned().ok_or(
            ExternalResolutionTraceError::UnknownSupport {
                row: row.index,
                support: row.support[1],
            },
        )?;
        let pivot_var = row
            .pivot
            .map(|pivot| pivot.unsigned_abs())
            .filter(|pivot| *pivot > 0)
            .ok_or(ExternalResolutionTraceError::MissingPivot { row: row.index })?;
        let pivot = pivot_var as Lit;

        if left_clause.contains(&-pivot) && right_clause.contains(&pivot) {
            std::mem::swap(&mut left_parent, &mut right_parent);
            std::mem::swap(&mut left_clause, &mut right_clause);
        }

        steps.push(ResolutionStep {
            left_parent,
            right_parent,
            pivot_var,
            resolvent: clause.clone(),
        });
        row_to_clause_id.insert(row.index, (formula.clauses.len() + steps.len()) as u32);
        row_to_clause.insert(row.index, clause);
    }

    validate_resolution_instance(formula, ResolutionProof { steps }).map_err(Into::into)
}

pub fn resolution_instance_from_unfolded_trace(
    unfolded_trace: &str,
) -> Result<ValidatedResolutionInstance, ExternalResolutionTraceError> {
    let parsed_rows = parse_unfolded_trace_rows(unfolded_trace)?;
    let clauses = parsed_rows
        .iter()
        .filter(|row| row.support.is_empty())
        .map(|row| normalize_clause(&row.clause))
        .collect::<Vec<_>>();
    let num_vars = parsed_rows
        .iter()
        .flat_map(|row| row.clause.iter().copied().chain(row.pivot))
        .map(Lit::unsigned_abs)
        .max()
        .unwrap_or(0);
    let formula = CnfFormula { num_vars, clauses };

    validate_resolution_instance_from_unfolded_trace(&formula, unfolded_trace)
}

pub fn generate_resolution_proof_by_closure(
    formula: &CnfFormula,
    max_steps: usize,
) -> Result<ResolutionProof, Phase2Error> {
    let mut clauses = formula.clauses.clone();
    let mut known = std::collections::BTreeMap::<Vec<Lit>, u32>::new();
    for (index, clause) in clauses.iter().enumerate() {
        known.insert(clause.clone(), (index + 1) as u32);
    }

    let mut steps = Vec::new();
    let mut cursor = 0usize;

    while cursor < clauses.len() {
        let left_clause = clauses[cursor].clone();
        for right_index in 0..=cursor {
            let right_clause = clauses[right_index].clone();
            let parent_pairs = [(&left_clause, &right_clause), (&right_clause, &left_clause)];
            for (ordered_left, ordered_right) in parent_pairs {
                for pivot_var in candidate_pivots(ordered_left, ordered_right) {
                    let resolvent = resolve_clauses(ordered_left, ordered_right, pivot_var);
                    if is_tautology(&resolvent) {
                        continue;
                    }
                    if known.contains_key(&resolvent) {
                        continue;
                    }

                    let left_id = *known.get(ordered_left).expect("left clause id exists");
                    let right_id = *known.get(ordered_right).expect("right clause id exists");

                    steps.push(ResolutionStep {
                        left_parent: left_id,
                        right_parent: right_id,
                        pivot_var,
                        resolvent: resolvent.clone(),
                    });

                    let new_id = (clauses.len() + 1) as u32;
                    known.insert(resolvent.clone(), new_id);
                    clauses.push(resolvent.clone());

                    if resolvent.is_empty() {
                        return Ok(ResolutionProof { steps });
                    }
                    if steps.len() >= max_steps {
                        return Err(Phase2Error::ResolutionLimit(max_steps));
                    }
                }
            }
        }
        cursor += 1;
    }

    Err(Phase2Error::ResolutionLimit(max_steps))
}

#[cfg(feature = "backend-solver")]
pub fn solve_formula(formula: &CnfFormula) -> Result<SatOutcome, Phase2Error> {
    use varisat::{ExtendFormula, Lit as VarisatLit, Solver, Var};

    let mut solver = Solver::new();

    for clause in &formula.clauses {
        let mapped = clause
            .iter()
            .map(|lit| {
                let index = lit.unsigned_abs() as usize - 1;
                let var = Var::from_index(index);
                if *lit > 0 {
                    VarisatLit::positive(var)
                } else {
                    VarisatLit::negative(var)
                }
            })
            .collect::<Vec<_>>();
        solver.add_clause(&mapped);
    }

    if solver
        .solve()
        .map_err(|_| Phase2Error::UnsatWithoutResolution)?
    {
        let mut assignment = vec![false; formula.num_vars as usize];
        for lit in solver.model().unwrap_or_default() {
            assignment[lit.var().index()] = lit.is_positive();
        }
        validate_sat_instance(formula, &assignment).map(SatOutcome::Sat)
    } else {
        let proof = generate_resolution_proof_by_closure(
            formula,
            (formula.clauses.len().max(1) * 64) as usize,
        )?;
        validate_resolution_instance(formula, proof).map(SatOutcome::Unsat)
    }
}

pub(crate) fn commitment_literal_value(lit: Lit) -> u64 {
    if lit == 0 {
        0
    } else if lit > 0 {
        lit as u64
    } else {
        COMMIT_FIELD_MODULUS - ((-lit) as u64 % COMMIT_FIELD_MODULUS)
    }
}

#[cfg(test)]
fn canonical_commitment_formula(formula: &CnfFormula) -> CnfFormula {
    CnfFormula {
        num_vars: formula.num_vars,
        clauses: formula
            .clauses
            .iter()
            .map(|clause| {
                let mut normalized = clause.clone();
                normalized.sort_unstable();
                normalized.dedup();
                normalized
            })
            .collect(),
    }
}

fn commitment_slot_weights(max_clause_width: usize, slot_scale: u64) -> Vec<u64> {
    (0..max_clause_width)
        .map(|position| field_mul((position + 1) as u64, slot_scale))
        .collect()
}

fn clause_weight_pair(
    clause_index: u64,
    clause: &[Lit],
    slot_weights_a: &[u64],
    slot_weights_b: &[u64],
) -> (u64, u64) {
    let clause_len = clause.len() as u64;
    let mut mix_a = field_add(
        field_mul(clause_index, COMMIT_INDEX_SCALE_A),
        field_mul(clause_len, COMMIT_LEN_SCALE_A),
    );
    let mut mix_b = field_add(
        field_mul(clause_index, COMMIT_INDEX_SCALE_B),
        field_mul(clause_len, COMMIT_LEN_SCALE_B),
    );

    for (position, lit) in clause.iter().enumerate() {
        let lit_value = commitment_literal_value(*lit);
        mix_a = field_add(mix_a, field_mul(lit_value, slot_weights_a[position]));
        mix_b = field_add(mix_b, field_mul(lit_value, slot_weights_b[position]));
    }

    (mix_a, mix_b)
}

#[inline]
fn field_add(lhs: u64, rhs: u64) -> u64 {
    debug_assert!(lhs < COMMIT_FIELD_MODULUS);
    debug_assert!(rhs < COMMIT_FIELD_MODULUS);
    let sum = lhs + rhs;
    if sum >= COMMIT_FIELD_MODULUS {
        sum - COMMIT_FIELD_MODULUS
    } else {
        sum
    }
}

#[inline]
fn field_mul(lhs: u64, rhs: u64) -> u64 {
    debug_assert!(lhs < COMMIT_FIELD_MODULUS);
    debug_assert!(rhs < COMMIT_FIELD_MODULUS);
    (lhs * rhs) % COMMIT_FIELD_MODULUS
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedUnfoldedTraceRow {
    index: usize,
    clause: Vec<Lit>,
    support: Vec<usize>,
    pivot: Option<Lit>,
}

fn parse_unfolded_trace_rows(
    unfolded_trace: &str,
) -> Result<Vec<ParsedUnfoldedTraceRow>, ExternalResolutionTraceError> {
    let mut rows = Vec::new();

    for (line_index, raw_line) in unfolded_trace.lines().enumerate() {
        let line_no = line_index + 1;
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with("DEGREE:") {
            continue;
        }

        let tokens = line.split_whitespace().collect::<Vec<_>>();
        let clause_marker = tokens
            .iter()
            .position(|token| *token == "clause:")
            .ok_or_else(|| ExternalResolutionTraceError::MalformedLine {
                line: line_no,
                reason: "missing `clause:` marker".to_owned(),
            })?;
        let support_marker = tokens
            .iter()
            .position(|token| *token == "support:")
            .ok_or_else(|| ExternalResolutionTraceError::MalformedLine {
                line: line_no,
                reason: "missing `support:` marker".to_owned(),
            })?;
        let pivot_marker = tokens
            .iter()
            .position(|token| *token == "pivot:")
            .ok_or_else(|| ExternalResolutionTraceError::MalformedLine {
                line: line_no,
                reason: "missing `pivot:` marker".to_owned(),
            })?;
        let end_marker = tokens
            .iter()
            .position(|token| *token == "end:")
            .ok_or_else(|| ExternalResolutionTraceError::MalformedLine {
                line: line_no,
                reason: "missing `end:` marker".to_owned(),
            })?;

        if tokens.first() != Some(&"index:") || clause_marker != 2 {
            return Err(ExternalResolutionTraceError::MalformedLine {
                line: line_no,
                reason: "expected `index: <n> clause:` prefix".to_owned(),
            });
        }
        if !(clause_marker < support_marker
            && support_marker < pivot_marker
            && pivot_marker < end_marker)
        {
            return Err(ExternalResolutionTraceError::MalformedLine {
                line: line_no,
                reason: "markers appear out of order".to_owned(),
            });
        }

        let index = tokens[1].parse::<usize>().map_err(|err| {
            ExternalResolutionTraceError::MalformedLine {
                line: line_no,
                reason: format!("invalid row index: {err}"),
            }
        })?;
        let clause = tokens[clause_marker + 1..support_marker]
            .iter()
            .filter(|token| **token != "0")
            .map(|token| {
                token
                    .parse::<Lit>()
                    .map_err(|err| ExternalResolutionTraceError::MalformedLine {
                        line: line_no,
                        reason: format!("invalid clause literal `{token}`: {err}"),
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let support = tokens[support_marker + 1..pivot_marker]
            .iter()
            .map(|token| {
                token
                    .parse::<usize>()
                    .map_err(|err| ExternalResolutionTraceError::MalformedLine {
                        line: line_no,
                        reason: format!("invalid support row `{token}`: {err}"),
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let pivot_tokens = &tokens[pivot_marker + 1..end_marker];
        let pivot = match pivot_tokens {
            [] => None,
            [pivot] => Some(pivot.parse::<Lit>().map_err(|err| {
                ExternalResolutionTraceError::MalformedLine {
                    line: line_no,
                    reason: format!("invalid pivot literal `{pivot}`: {err}"),
                }
            })?),
            _ => {
                return Err(ExternalResolutionTraceError::MalformedLine {
                    line: line_no,
                    reason: "expected at most one pivot literal per unfolded row".to_owned(),
                });
            }
        };

        rows.push(ParsedUnfoldedTraceRow {
            index,
            clause,
            support,
            pivot,
        });
    }

    Ok(rows)
}

fn clause_by_id(clauses: &[Vec<Lit>], id: u32) -> Result<Vec<Lit>, Phase2Error> {
    clauses
        .get(id.saturating_sub(1) as usize)
        .cloned()
        .ok_or(Phase2Error::UnknownClause(id))
}

fn normalize_clause(clause: &[Lit]) -> Vec<Lit> {
    let mut normalized = clause.to_vec();
    normalized.sort_unstable();
    normalized.dedup();
    normalized
}

fn candidate_pivots(left: &[Lit], right: &[Lit]) -> Vec<u32> {
    let left_set = left
        .iter()
        .copied()
        .collect::<std::collections::BTreeSet<_>>();
    let right_set = right
        .iter()
        .copied()
        .collect::<std::collections::BTreeSet<_>>();
    left_set
        .iter()
        .filter_map(|lit| {
            if *lit > 0 && right_set.contains(&-*lit) {
                Some(*lit as u32)
            } else {
                None
            }
        })
        .collect()
}

fn resolve_clauses(left: &[Lit], right: &[Lit], pivot_var: u32) -> Vec<Lit> {
    let pivot = pivot_var as Lit;
    let mut resolvent = left
        .iter()
        .copied()
        .filter(|lit| *lit != pivot)
        .chain(right.iter().copied().filter(|lit| *lit != -pivot))
        .collect::<Vec<_>>();
    resolvent.sort_unstable();
    resolvent.dedup();
    resolvent
}

fn is_tautology(clause: &[Lit]) -> bool {
    clause
        .iter()
        .any(|lit| clause.binary_search(&-*lit).is_ok())
}

fn eval_lit(lit: Lit, assignment: &[bool]) -> bool {
    let value = assignment[lit.unsigned_abs() as usize - 1];
    if lit > 0 {
        value
    } else {
        !value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use resolution_verifier_core::verify_flat_resolution_witness;

    fn unsat_formula() -> CnfFormula {
        CnfFormula {
            num_vars: 1,
            clauses: vec![vec![1], vec![-1]],
        }
    }

    fn reference_field_add(lhs: u64, rhs: u64) -> u64 {
        ((lhs as u128 + rhs as u128) % COMMIT_FIELD_MODULUS as u128) as u64
    }

    fn reference_field_mul(lhs: u64, rhs: u64) -> u64 {
        ((lhs as u128 * rhs as u128) % COMMIT_FIELD_MODULUS as u128) as u64
    }

    fn reference_formula_commitment(formula: &CnfFormula) -> FormulaCommitment {
        let canonical = canonical_commitment_formula(formula);
        let max_clause_width = canonical
            .clauses
            .iter()
            .map(|clause| clause.len() as u32)
            .max()
            .unwrap_or(0);

        let mut mix_a = 0u64;
        let mut mix_b = 0u64;

        for (index, clause) in canonical.clauses.iter().enumerate() {
            let clause_index = (index + 1) as u64;
            let mut clause_mix_a = reference_field_mul(clause_index, COMMIT_INDEX_SCALE_A);
            clause_mix_a = reference_field_add(
                clause_mix_a,
                reference_field_mul(clause.len() as u64, COMMIT_LEN_SCALE_A),
            );
            let mut clause_mix_b = reference_field_mul(clause_index, COMMIT_INDEX_SCALE_B);
            clause_mix_b = reference_field_add(
                clause_mix_b,
                reference_field_mul(clause.len() as u64, COMMIT_LEN_SCALE_B),
            );

            for position in 0..max_clause_width as usize {
                let lit_value = clause
                    .get(position)
                    .copied()
                    .map(commitment_literal_value)
                    .unwrap_or(0);
                clause_mix_a = reference_field_add(
                    clause_mix_a,
                    reference_field_mul(
                        lit_value,
                        reference_field_mul((position + 1) as u64, COMMIT_SLOT_SCALE_A),
                    ),
                );
                clause_mix_b = reference_field_add(
                    clause_mix_b,
                    reference_field_mul(
                        lit_value,
                        reference_field_mul((position + 1) as u64, COMMIT_SLOT_SCALE_B),
                    ),
                );
            }

            mix_a = reference_field_add(
                reference_field_mul(mix_a, COMMIT_ROOT_ALPHA_A),
                clause_mix_a,
            );
            mix_b = reference_field_add(
                reference_field_mul(mix_b, COMMIT_ROOT_ALPHA_B),
                clause_mix_b,
            );
        }

        FormulaCommitment {
            num_vars: formula.num_vars,
            num_clauses: formula.clauses.len() as u32,
            max_clause_width,
            mix_a: mix_a as u32,
            mix_b: mix_b as u32,
        }
    }

    #[test]
    fn optimized_formula_commitment_matches_reference_algorithm() {
        let formula = CnfFormula {
            num_vars: 7,
            clauses: vec![
                vec![3, -1, 3, 2],
                vec![-4, 2],
                vec![6, -6, 6, 5, -2],
                vec![],
            ],
        };

        assert_eq!(
            FormulaCommitment::from_formula(&formula).unwrap(),
            reference_formula_commitment(&formula)
        );
    }

    #[test]
    fn validates_sat_assignment() {
        let formula = CnfFormula {
            num_vars: 2,
            clauses: vec![vec![1, -2], vec![2]],
        };
        let instance = validate_sat_instance(&formula, &[true, true]).unwrap();
        assert_eq!(instance.commitment.num_clauses, 2);
        assert!(instance
            .clause_truth_rows
            .iter()
            .all(|row| row.iter().any(|bit| *bit)));
    }

    #[test]
    fn derives_and_validates_simple_resolution_proof() {
        let proof = generate_resolution_proof_by_closure(&unsat_formula(), 8).unwrap();
        let instance = validate_resolution_instance(&unsat_formula(), proof).unwrap();
        assert_eq!(instance.expanded_steps.len(), 1);
        assert!(instance.expanded_steps[0].resolvent.is_empty());
    }

    #[test]
    fn resolution_removes_only_oriented_pivot_literals() {
        assert_eq!(resolve_clauses(&[1, -1], &[1, -1], 1), vec![-1, 1]);
    }

    #[test]
    fn rejects_empty_resolvent_from_tautological_parents() {
        let formula = CnfFormula {
            num_vars: 1,
            clauses: vec![vec![-1, 1], vec![-1, 1]],
        };
        let proof = ResolutionProof {
            steps: vec![ResolutionStep {
                left_parent: 1,
                right_parent: 2,
                pivot_var: 1,
                resolvent: vec![],
            }],
        };

        let err = validate_resolution_instance(&formula, proof).unwrap_err();
        assert!(matches!(err, Phase2Error::BadResolvent { step: 0 }));
    }

    #[test]
    fn validates_unfolded_trace_against_source_formula() {
        let formula = CnfFormula {
            num_vars: 1,
            clauses: vec![vec![-1], vec![1], vec![1]],
        };
        let trace = "\
index:  0  clause:  1  support:    pivot:   end:  0
index:  1  clause:  -1  support:    pivot:   end:  0
index:  2  clause:    support:  0 1  pivot:  1 end:  0
DEGREE: 4
";

        let instance = validate_resolution_instance_from_unfolded_trace(&formula, trace).unwrap();
        assert_eq!(instance.proof.steps.len(), 1);
        assert_eq!(instance.formula.clauses.len(), 3);
        assert!(instance.expanded_steps[0].resolvent.is_empty());
    }

    #[test]
    fn reconstructs_resolution_instance_from_unfolded_trace() {
        let trace = "\
index:  0  clause:  1  support:    pivot:   end:  0
index:  1  clause:  -1  support:    pivot:   end:  0
index:  2  clause:    support:  0 1  pivot:  1 end:  0
DEGREE: 4
";

        let instance = resolution_instance_from_unfolded_trace(trace).unwrap();
        assert_eq!(instance.formula.num_vars, 1);
        assert_eq!(instance.formula.clauses.len(), 2);
        assert_eq!(instance.proof.steps.len(), 1);
        assert!(instance.expanded_steps[0].resolvent.is_empty());
    }

    #[test]
    fn normalizes_resolvents_inside_validated_witness() {
        let formula = unsat_formula();
        let proof = ResolutionProof {
            steps: vec![ResolutionStep {
                left_parent: 1,
                right_parent: 2,
                pivot_var: 1,
                resolvent: vec![0; 0],
            }],
        };

        let instance = validate_resolution_instance(&formula, proof).unwrap();
        let summary = verify_flat_resolution_witness(&instance.flat_witness()).unwrap();
        assert_eq!(summary.initial_clause_count, 2);
        assert_eq!(summary.resolution_steps, 1);
    }

    #[test]
    fn rejects_unfolded_trace_with_unknown_initial_clause() {
        let trace = "\
index:  0  clause:  1  support:    pivot:   end:  0
index:  1  clause:  2  support:    pivot:   end:  0
index:  2  clause:    support:  0 1  pivot:  1 end:  0
";

        let err =
            validate_resolution_instance_from_unfolded_trace(&unsat_formula(), trace).unwrap_err();
        assert!(matches!(
            err,
            ExternalResolutionTraceError::UnknownInitialClause { row: 1 }
        ));
    }

    #[test]
    fn accepts_unfolded_trace_when_parent_order_is_reversed() {
        let trace = "\
index:  0  clause:  -1  support:    pivot:   end:  0
index:  1  clause:  1  support:    pivot:   end:  0
index:  2  clause:    support:  0 1  pivot:  -1 end:  0
";

        let instance =
            validate_resolution_instance_from_unfolded_trace(&unsat_formula(), trace).unwrap();
        assert_eq!(instance.proof.steps.len(), 1);
        assert_eq!(instance.proof.steps[0].left_parent, 1);
        assert_eq!(instance.proof.steps[0].right_parent, 2);
    }

    #[test]
    fn flat_witness_round_trips_into_core_verifier() {
        let proof = generate_resolution_proof_by_closure(&unsat_formula(), 8).unwrap();
        let instance = validate_resolution_instance(&unsat_formula(), proof).unwrap();
        let summary = verify_flat_resolution_witness(&instance.flat_witness()).unwrap();
        assert_eq!(summary.initial_clause_count, 2);
        assert_eq!(summary.resolution_steps, 1);
        assert_eq!(summary.max_clause_width, 1);
    }
}
