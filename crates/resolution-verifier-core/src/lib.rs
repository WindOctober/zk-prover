#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use alloc::vec::Vec;
use core::{cmp::Ordering, fmt};
use serde::{Deserialize, Serialize};

pub type Lit = i32;
const WORD_ENCODING_VERSION: u64 = 1;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FlatResolutionWitness {
    pub num_vars: u32,
    pub initial_clause_offsets: Vec<u32>,
    pub initial_clause_literals: Vec<Lit>,
    pub step_left_parents: Vec<u32>,
    pub step_right_parents: Vec<u32>,
    pub step_pivot_vars: Vec<u32>,
    pub step_resolvent_offsets: Vec<u32>,
    pub step_resolvent_literals: Vec<Lit>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolutionVerificationSummary {
    pub num_vars: u32,
    pub initial_clause_count: u32,
    pub resolution_steps: u32,
    pub max_clause_width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolutionVerificationError {
    BadClauseOffsets,
    UnknownClause(u32),
    MissingPivot { step: usize, pivot: u32 },
    BadResolvent { step: usize },
    MissingEmptyClause,
    LiteralOutOfRange { lit: Lit, num_vars: u32 },
    PivotOutOfRange { pivot: u32, num_vars: u32 },
    BadWordEncoding,
    WordOutOfRange { value: u64, target: &'static str },
}

impl fmt::Display for ResolutionVerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadClauseOffsets => write!(f, "witness clause offset vector is malformed"),
            Self::UnknownClause(id) => {
                write!(f, "resolution proof references an unknown clause id {id}")
            }
            Self::MissingPivot { step, pivot } => {
                write!(
                    f,
                    "resolution proof step {step} does not resolve on pivot x{pivot}"
                )
            }
            Self::BadResolvent { step } => {
                write!(
                    f,
                    "resolution proof step {step} resolvent does not match the parents"
                )
            }
            Self::MissingEmptyClause => {
                write!(f, "resolution proof does not derive the empty clause")
            }
            Self::LiteralOutOfRange { lit, num_vars } => {
                write!(f, "literal {lit} is out of range for {num_vars} variables")
            }
            Self::PivotOutOfRange { pivot, num_vars } => {
                write!(f, "pivot {pivot} is out of range for {num_vars} variables")
            }
            Self::BadWordEncoding => write!(f, "witness word encoding is malformed"),
            Self::WordOutOfRange { value, target } => {
                write!(f, "witness word value {value} does not fit into {target}")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ResolutionVerificationError {}

pub fn verify_flat_resolution_witness(
    witness: &FlatResolutionWitness,
) -> Result<ResolutionVerificationSummary, ResolutionVerificationError> {
    let initial_clauses = decode_clauses(
        &witness.initial_clause_offsets,
        &witness.initial_clause_literals,
        witness.num_vars,
    )?;
    let resolvents = decode_clauses(
        &witness.step_resolvent_offsets,
        &witness.step_resolvent_literals,
        witness.num_vars,
    )?;

    if ![
        witness.step_left_parents.len(),
        witness.step_right_parents.len(),
        witness.step_pivot_vars.len(),
        resolvents.len(),
    ]
    .windows(2)
    .all(|pair| pair[0] == pair[1])
    {
        return Err(ResolutionVerificationError::BadClauseOffsets);
    }

    let mut known = initial_clauses.clone();
    let mut max_clause_width = initial_clauses
        .iter()
        .map(|clause| clause.len() as u32)
        .max()
        .unwrap_or(0);

    for step_index in 0..resolvents.len() {
        let left = clause_by_id(&known, witness.step_left_parents[step_index])?;
        let right = clause_by_id(&known, witness.step_right_parents[step_index])?;
        let pivot_var = witness.step_pivot_vars[step_index];
        if pivot_var == 0 || pivot_var > witness.num_vars {
            return Err(ResolutionVerificationError::PivotOutOfRange {
                pivot: pivot_var,
                num_vars: witness.num_vars,
            });
        }
        let pivot = pivot_var as Lit;
        if !left.contains(&pivot) || !right.contains(&-pivot) {
            return Err(ResolutionVerificationError::MissingPivot {
                step: step_index,
                pivot: pivot_var,
            });
        }

        let expected = resolve_clauses(&left, &right, pivot_var);
        let resolvent = &resolvents[step_index];
        if expected != *resolvent {
            return Err(ResolutionVerificationError::BadResolvent { step: step_index });
        }

        max_clause_width = max_clause_width.max(resolvent.len() as u32);
        known.push(resolvent.clone());
    }

    if known
        .last()
        .map(|clause| !clause.is_empty())
        .unwrap_or(true)
    {
        return Err(ResolutionVerificationError::MissingEmptyClause);
    }

    Ok(ResolutionVerificationSummary {
        num_vars: witness.num_vars,
        initial_clause_count: initial_clauses.len() as u32,
        resolution_steps: resolvents.len() as u32,
        max_clause_width,
    })
}

pub fn encode_witness_words(witness: &FlatResolutionWitness) -> Vec<u64> {
    let step_count = witness.step_left_parents.len();
    let mut words = Vec::with_capacity(
        7 + witness.initial_clause_offsets.len()
            + witness.initial_clause_literals.len()
            + witness.step_left_parents.len()
            + witness.step_right_parents.len()
            + witness.step_pivot_vars.len()
            + witness.step_resolvent_offsets.len()
            + witness.step_resolvent_literals.len(),
    );
    words.extend_from_slice(&[
        WORD_ENCODING_VERSION,
        witness.num_vars as u64,
        witness.initial_clause_offsets.len() as u64,
        witness.initial_clause_literals.len() as u64,
        step_count as u64,
        witness.step_resolvent_offsets.len() as u64,
        witness.step_resolvent_literals.len() as u64,
    ]);
    words.extend(
        witness
            .initial_clause_offsets
            .iter()
            .map(|value| *value as u64),
    );
    words.extend(
        witness
            .initial_clause_literals
            .iter()
            .map(|value| (*value as i64) as u64),
    );
    words.extend(witness.step_left_parents.iter().map(|value| *value as u64));
    words.extend(witness.step_right_parents.iter().map(|value| *value as u64));
    words.extend(witness.step_pivot_vars.iter().map(|value| *value as u64));
    words.extend(
        witness
            .step_resolvent_offsets
            .iter()
            .map(|value| *value as u64),
    );
    words.extend(
        witness
            .step_resolvent_literals
            .iter()
            .map(|value| (*value as i64) as u64),
    );
    words
}

pub fn decode_witness_words(
    words: &[u64],
) -> Result<FlatResolutionWitness, ResolutionVerificationError> {
    if words.len() < 7 || words[0] != WORD_ENCODING_VERSION {
        return Err(ResolutionVerificationError::BadWordEncoding);
    }

    let num_vars = u64_to_u32(words[1], "u32")?;
    let initial_offsets_len = u64_to_usize(words[2], "usize")?;
    let initial_literals_len = u64_to_usize(words[3], "usize")?;
    let step_count = u64_to_usize(words[4], "usize")?;
    let step_offsets_len = u64_to_usize(words[5], "usize")?;
    let step_literals_len = u64_to_usize(words[6], "usize")?;

    if step_offsets_len != step_count + 1 {
        return Err(ResolutionVerificationError::BadWordEncoding);
    }

    let expected_len = 7
        + initial_offsets_len
        + initial_literals_len
        + step_count
        + step_count
        + step_count
        + step_offsets_len
        + step_literals_len;
    if words.len() != expected_len {
        return Err(ResolutionVerificationError::BadWordEncoding);
    }

    let mut cursor = 7;
    let initial_clause_offsets = decode_u32_slice(words, &mut cursor, initial_offsets_len, "u32")?;
    let initial_clause_literals = decode_lit_slice(words, &mut cursor, initial_literals_len)?;
    let step_left_parents = decode_u32_slice(words, &mut cursor, step_count, "u32")?;
    let step_right_parents = decode_u32_slice(words, &mut cursor, step_count, "u32")?;
    let step_pivot_vars = decode_u32_slice(words, &mut cursor, step_count, "u32")?;
    let step_resolvent_offsets = decode_u32_slice(words, &mut cursor, step_offsets_len, "u32")?;
    let step_resolvent_literals = decode_lit_slice(words, &mut cursor, step_literals_len)?;

    Ok(FlatResolutionWitness {
        num_vars,
        initial_clause_offsets,
        initial_clause_literals,
        step_left_parents,
        step_right_parents,
        step_pivot_vars,
        step_resolvent_offsets,
        step_resolvent_literals,
    })
}

pub fn verify_witness_words(
    words: &[u64],
) -> Result<ResolutionVerificationSummary, ResolutionVerificationError> {
    let witness = decode_witness_words(words)?;
    verify_flat_resolution_witness(&witness)
}

fn decode_clauses(
    offsets: &[u32],
    literals: &[Lit],
    num_vars: u32,
) -> Result<Vec<Vec<Lit>>, ResolutionVerificationError> {
    if offsets.first().copied() != Some(0) {
        return Err(ResolutionVerificationError::BadClauseOffsets);
    }
    let mut clauses = Vec::with_capacity(offsets.len().saturating_sub(1));
    for window in offsets.windows(2) {
        let start = window[0] as usize;
        let end = window[1] as usize;
        if start > end || end > literals.len() {
            return Err(ResolutionVerificationError::BadClauseOffsets);
        }
        let normalized = normalize_clause(&literals[start..end], num_vars)?;
        clauses.push(normalized);
    }
    Ok(clauses)
}

fn clause_by_id(clauses: &[Vec<Lit>], id: u32) -> Result<Vec<Lit>, ResolutionVerificationError> {
    clauses
        .get(id.saturating_sub(1) as usize)
        .cloned()
        .ok_or(ResolutionVerificationError::UnknownClause(id))
}

fn decode_u32_slice(
    words: &[u64],
    cursor: &mut usize,
    len: usize,
    target: &'static str,
) -> Result<Vec<u32>, ResolutionVerificationError> {
    let end = cursor.saturating_add(len);
    if end > words.len() {
        return Err(ResolutionVerificationError::BadWordEncoding);
    }
    let decoded = words[*cursor..end]
        .iter()
        .copied()
        .map(|value| u64_to_u32(value, target))
        .collect::<Result<Vec<_>, _>>()?;
    *cursor = end;
    Ok(decoded)
}

fn decode_lit_slice(
    words: &[u64],
    cursor: &mut usize,
    len: usize,
) -> Result<Vec<Lit>, ResolutionVerificationError> {
    let end = cursor.saturating_add(len);
    if end > words.len() {
        return Err(ResolutionVerificationError::BadWordEncoding);
    }
    let decoded = words[*cursor..end]
        .iter()
        .copied()
        .map(u64_to_lit)
        .collect::<Result<Vec<_>, _>>()?;
    *cursor = end;
    Ok(decoded)
}

fn u64_to_u32(value: u64, target: &'static str) -> Result<u32, ResolutionVerificationError> {
    u32::try_from(value).map_err(|_| ResolutionVerificationError::WordOutOfRange { value, target })
}

fn u64_to_usize(value: u64, target: &'static str) -> Result<usize, ResolutionVerificationError> {
    usize::try_from(value)
        .map_err(|_| ResolutionVerificationError::WordOutOfRange { value, target })
}

fn u64_to_lit(value: u64) -> Result<Lit, ResolutionVerificationError> {
    let signed = value as i64;
    i32::try_from(signed).map_err(|_| ResolutionVerificationError::WordOutOfRange {
        value,
        target: "i32",
    })
}

fn normalize_clause(
    clause: &[Lit],
    num_vars: u32,
) -> Result<Vec<Lit>, ResolutionVerificationError> {
    let mut normalized = clause.to_vec();
    normalized.sort_unstable_by(canonical_lit_order);
    normalized.dedup();
    for &lit in &normalized {
        let abs = lit.unsigned_abs();
        if abs == 0 || abs > num_vars {
            return Err(ResolutionVerificationError::LiteralOutOfRange { lit, num_vars });
        }
    }
    Ok(normalized)
}

fn canonical_lit_order(left: &Lit, right: &Lit) -> Ordering {
    left.cmp(right)
}

fn resolve_clauses(left: &[Lit], right: &[Lit], pivot_var: u32) -> Vec<Lit> {
    let pivot = pivot_var as Lit;
    let mut resolvent = left
        .iter()
        .copied()
        .filter(|lit| *lit != pivot)
        .chain(right.iter().copied().filter(|lit| *lit != -pivot))
        .collect::<Vec<_>>();
    resolvent.sort_unstable_by(canonical_lit_order);
    resolvent.dedup();
    resolvent
}

#[cfg(test)]
mod tests {
    use super::*;

    fn simple_witness() -> FlatResolutionWitness {
        FlatResolutionWitness {
            num_vars: 1,
            initial_clause_offsets: vec![0, 1, 2],
            initial_clause_literals: vec![1, -1],
            step_left_parents: vec![1],
            step_right_parents: vec![2],
            step_pivot_vars: vec![1],
            step_resolvent_offsets: vec![0, 0],
            step_resolvent_literals: vec![],
        }
    }

    #[test]
    fn verifies_simple_resolution_chain() {
        let summary = verify_flat_resolution_witness(&simple_witness()).unwrap();
        assert_eq!(summary.initial_clause_count, 2);
        assert_eq!(summary.resolution_steps, 1);
        assert_eq!(summary.max_clause_width, 1);
    }

    #[test]
    fn rejects_bad_resolvent() {
        let mut witness = simple_witness();
        witness.step_resolvent_offsets = vec![0, 1];
        witness.step_resolvent_literals = vec![1];
        let err = verify_flat_resolution_witness(&witness).unwrap_err();
        assert_eq!(err, ResolutionVerificationError::BadResolvent { step: 0 });
    }

    #[test]
    fn resolution_removes_only_oriented_pivot_literals() {
        assert_eq!(resolve_clauses(&[1, -1], &[1, -1], 1), vec![-1, 1]);
    }

    #[test]
    fn rejects_empty_resolvent_from_tautological_parents() {
        let witness = FlatResolutionWitness {
            num_vars: 1,
            initial_clause_offsets: vec![0, 2, 4],
            initial_clause_literals: vec![-1, 1, -1, 1],
            step_left_parents: vec![1],
            step_right_parents: vec![2],
            step_pivot_vars: vec![1],
            step_resolvent_offsets: vec![0, 0],
            step_resolvent_literals: vec![],
        };

        let err = verify_flat_resolution_witness(&witness).unwrap_err();
        assert_eq!(err, ResolutionVerificationError::BadResolvent { step: 0 });
    }

    #[test]
    fn witness_word_round_trip() {
        let witness = simple_witness();
        let words = encode_witness_words(&witness);
        let decoded = decode_witness_words(&words).unwrap();
        assert_eq!(decoded, witness);
        let summary = verify_witness_words(&words).unwrap();
        assert_eq!(summary.resolution_steps, 1);
    }
}
