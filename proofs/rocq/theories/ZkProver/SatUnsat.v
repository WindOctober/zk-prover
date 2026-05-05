From Coq Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.

Import ListNotations.

Set Implicit Arguments.

Module CircuitSoundness.

Definition var := nat.

Inductive lit : Type :=
| Pos : var -> lit
| Neg : var -> lit.

Lemma lit_eq_dec : forall x y : lit, {x = y} + {x <> y}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition clause := list lit.
Definition cnf := list clause.
Definition assignment := var -> bool.

Definition lit_eval (a : assignment) (l : lit) : bool :=
  match l with
  | Pos v => a v
  | Neg v => negb (a v)
  end.

Definition clause_holds (a : assignment) (c : clause) : Prop :=
  exists j l, nth_error c j = Some l /\ lit_eval a l = true.

Definition cnf_holds (a : assignment) (f : cnf) : Prop :=
  forall c, In c f -> clause_holds a c.

Definition matrix (A : Type) := nat -> nat -> option A.

Record SatCircuitWitness := {
  sat_assignment : assignment;
  sat_truth_matrix : matrix bool
}.

Definition sat_row_matches_clause
    (a : assignment) (truth : matrix bool) (row : nat) (c : clause) : Prop :=
  forall j l,
    nth_error c j = Some l ->
    truth row j = Some (lit_eval a l).

Definition sat_clause_gate
    (truth : matrix bool) (row : nat) (c : clause) : Prop :=
  exists j l,
    nth_error c j = Some l /\
    truth row j = Some true.

Definition sat_circuit_constraints (f : cnf) (w : SatCircuitWitness) : Prop :=
  forall row c,
    nth_error f row = Some c ->
    sat_row_matches_clause (sat_assignment w) (sat_truth_matrix w) row c /\
    sat_clause_gate (sat_truth_matrix w) row c.

Lemma in_nth_error_exists :
  forall (A : Type) (x : A) (xs : list A),
    In x xs -> exists n, nth_error xs n = Some x.
Proof.
  intros A x xs Hin.
  induction xs as [| y ys IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst. exists 0. reflexivity.
    + destruct (IH Hin) as [n Hn].
      exists (S n). exact Hn.
Qed.

Theorem sat_constraints_sound :
  forall f w,
    sat_circuit_constraints f w ->
    cnf_holds (sat_assignment w) f.
Proof.
  intros f w Hconstraints c Hin.
  destruct (@in_nth_error_exists clause c f Hin) as [row Hrow].
  specialize (Hconstraints row c Hrow) as [Hrow_matches Hgate].
  destruct Hgate as [j [l [Hl Htruth]]].
  exists j, l. split; [exact Hl |].
  specialize (Hrow_matches j l Hl).
  rewrite Hrow_matches in Htruth.
  inversion Htruth. reflexivity.
Qed.

Definition all_clauses_hold (a : assignment) (clauses : list clause) : Prop :=
  forall c, In c clauses -> clause_holds a c.

Lemma cnf_holds_all_clauses_hold :
  forall a f, cnf_holds a f -> all_clauses_hold a f.
Proof.
  unfold cnf_holds, all_clauses_hold. auto.
Qed.

Record ResolutionStep := {
  left_parent : nat;
  right_parent : nat;
  pivot_var : var;
  step_resolvent : clause
}.

Definition clause_by_id (known : list clause) (id : nat) (c : clause) : Prop :=
  id > 0 /\ nth_error known (id - 1) = Some c.

Lemma clause_by_id_in :
  forall known id c,
    clause_by_id known id c ->
    In c known.
Proof.
  intros known id c [_ Hnth].
  apply nth_error_In with (n := id - 1). exact Hnth.
Qed.

Definition pivot_pos (p : var) : lit := Pos p.
Definition pivot_neg (p : var) : lit := Neg p.

Definition oriented_resolution_member
    (left right : clause) (pivot : var) (l : lit) : Prop :=
  (In l left /\ l <> pivot_pos pivot) \/
  (In l right /\ l <> pivot_neg pivot).

Definition resolves (left right : clause) (pivot : var) (resolvent : clause) : Prop :=
  In (pivot_pos pivot) left /\
  In (pivot_neg pivot) right /\
  forall l,
    In l resolvent <->
      oriented_resolution_member left right pivot l.

Fixpoint resolution_steps_valid (known : list clause) (steps : list ResolutionStep) : Prop :=
  match steps with
  | [] => True
  | step :: rest =>
      exists left right,
        clause_by_id known (left_parent step) left /\
        clause_by_id known (right_parent step) right /\
        resolves left right (pivot_var step) (step_resolvent step) /\
        resolution_steps_valid (known ++ [step_resolvent step]) rest
  end.

Definition final_step_empty (steps : list ResolutionStep) : Prop :=
  exists prefix step,
    steps = prefix ++ [step] /\
    step_resolvent step = [].

Definition resolution_refutation (f : cnf) (steps : list ResolutionStep) : Prop :=
  resolution_steps_valid f steps /\ final_step_empty steps.

Record ResolutionAirRow := {
  air_is_semantic : bool;
  air_is_derived : bool;
  air_entry_id : nat;
  air_left_id : nat;
  air_right_id : nat;
  air_pivot : var;
  air_current_clause : clause;
  air_left_clause : clause;
  air_right_clause : clause;
  air_left_keep_flags : list bool;
  air_right_keep_flags : list bool
}.

Inductive ResolutionTraceCell : Type :=
| CellBool : bool -> ResolutionTraceCell
| CellNat : nat -> ResolutionTraceCell
| CellLit : option lit -> ResolutionTraceCell.

Definition resolution_trace_matrix := matrix ResolutionTraceCell.

Definition RES_IS_SEMANTIC_COL := 0.
Definition RES_IS_TABLE_COL := 1.
Definition RES_IS_QUERY_COL := 2.
Definition RES_IS_DERIVED_COL := 3.
Definition RES_ENTRY_ID_COL := 4.
Definition RES_LEFT_ID_COL := 5.
Definition RES_RIGHT_ID_COL := 6.
Definition RES_PIVOT_COL := 7.
Definition RES_PIVOT_INV_COL := 8.
Definition RES_COMMIT_ACC_A_COL := 9.
Definition RES_COMMIT_ACC_B_COL := 10.
Definition RES_CLAUSE_MULT_COL := 16.
Definition RES_LEFT_ID_INV_COL := 26.
Definition RES_RIGHT_ID_INV_COL := 27.
Definition RES_LEFT_GAP_INV_COL := 28.
Definition RES_RIGHT_GAP_INV_COL := 29.
Definition RES_HEADER_WIDTH := 36.
Definition RES_FP_GAMMA_A := 1000 * 1000 + 3.
Definition RES_FP_GAMMA_B := 1000 * 1000 + 33.
Definition RES_RANGE_LIMBS := 2.
Definition RES_LITERAL_AUX_WIDTH := 2.

Definition res_current_lit_col (slot : nat) : nat :=
  RES_HEADER_WIDTH + slot.

Definition res_left_lit_col (width slot : nat) : nat :=
  RES_HEADER_WIDTH + width + slot.

Definition res_right_lit_col (width slot : nat) : nat :=
  RES_HEADER_WIDTH + width * 2 + slot.

Definition res_pivot_delta_base (width : nat) : nat :=
  RES_HEADER_WIDTH + width * 3.

Definition res_left_gap_base (width : nat) : nat :=
  res_pivot_delta_base width + RES_RANGE_LIMBS.

Definition res_right_gap_base (width : nat) : nat :=
  res_left_gap_base width + RES_RANGE_LIMBS.

Definition res_literal_aux_base (width clause_block slot : nat) : nat :=
  res_right_gap_base width
    + RES_RANGE_LIMBS
    + (clause_block * width + slot) * RES_LITERAL_AUX_WIDTH.

Definition res_literal_aux_end (width : nat) : nat :=
  RES_HEADER_WIDTH
    + width * 3
    + RES_RANGE_LIMBS
    + RES_RANGE_LIMBS
    + RES_RANGE_LIMBS
    + width * 3 * RES_LITERAL_AUX_WIDTH.

Definition res_left_pivot_eq_base (width : nat) : nat :=
  res_literal_aux_end width.

Definition res_left_pivot_inv_base (width : nat) : nat :=
  res_left_pivot_eq_base width + width.

Definition res_right_neg_pivot_eq_base (width : nat) : nat :=
  res_left_pivot_inv_base width + width.

Definition res_right_neg_pivot_inv_base (width : nat) : nat :=
  res_right_neg_pivot_eq_base width + width.

Definition res_left_keep_base (width : nat) : nat :=
  res_right_neg_pivot_inv_base width + width.

Definition res_right_keep_base (width : nat) : nat :=
  res_left_keep_base width + width.

Definition res_left_source_count_base (width : nat) : nat :=
  res_right_keep_base width + width.

Definition res_left_selected_count_base (width : nat) : nat :=
  res_left_source_count_base width + width.

Definition res_right_source_count_base (width : nat) : nat :=
  res_left_selected_count_base width + width.

Definition res_right_selected_count_base (width : nat) : nat :=
  res_right_source_count_base width + width.

Definition res_left_source_prod_a_base (width : nat) : nat :=
  res_right_selected_count_base width + width.

Definition res_left_source_prod_b_base (width : nat) : nat :=
  res_left_source_prod_a_base width + width.

Definition res_left_selected_prod_a_base (width : nat) : nat :=
  res_left_source_prod_b_base width + width.

Definition res_left_selected_prod_b_base (width : nat) : nat :=
  res_left_selected_prod_a_base width + width.

Definition res_right_source_prod_a_base (width : nat) : nat :=
  res_left_selected_prod_b_base width + width.

Definition res_right_source_prod_b_base (width : nat) : nat :=
  res_right_source_prod_a_base width + width.

Definition res_right_selected_prod_a_base (width : nat) : nat :=
  res_right_source_prod_b_base width + width.

Definition res_right_selected_prod_b_base (width : nat) : nat :=
  res_right_selected_prod_a_base width + width.

Definition resolution_trace_width (width : nat) : nat :=
  res_right_selected_prod_b_base width + width.

Definition trace_bool
    (trace : resolution_trace_matrix) (row col : nat) (value : bool) : Prop :=
  trace row col = Some (CellBool value).

Definition trace_nat
    (trace : resolution_trace_matrix) (row col value : nat) : Prop :=
  trace row col = Some (CellNat value).

Definition trace_lit
    (trace : resolution_trace_matrix) (row col : nat) (value : option lit) : Prop :=
  trace row col = Some (CellLit value).

Definition trace_clause_block
    (trace : resolution_trace_matrix)
    (row base width : nat)
    (c : clause) : Prop :=
  forall slot,
    slot < width ->
    trace_lit trace row (base + slot) (nth_error c slot).

Definition trace_flag_block
    (trace : resolution_trace_matrix)
    (row base width : nat)
    (flags : list bool) : Prop :=
  forall slot,
    slot < width ->
    trace_bool trace row (base + slot) (nth slot flags false).

Definition trace_nat_block
    (trace : resolution_trace_matrix)
    (row base width : nat)
    (values : list nat) : Prop :=
  forall slot,
    slot < width ->
    trace_nat trace row (base + slot) (nth slot values 0).

Definition option_lit_is_zero (value : option lit) : bool :=
  match value with
  | None => true
  | Some _ => false
  end.

Definition option_lit_eqb (value : option lit) (target : lit) : bool :=
  match value with
  | None => false
  | Some l => if lit_eq_dec l target then true else false
  end.

Definition lit_code (l : lit) : nat :=
  match l with
  | Pos v => S (2 * v)
  | Neg v => S (S (2 * v))
  end.

Definition option_lit_code (value : option lit) : nat :=
  match value with
  | None => 0
  | Some l => lit_code l
  end.

Definition bool_to_nat (b : bool) : nat :=
  if b then 1 else 0.

Fixpoint count_slots (n : nat) (active : nat -> bool) : nat :=
  match n with
  | 0 => 0
  | S k => count_slots k active + bool_to_nat (active k)
  end.

Definition fingerprint_term
    (gamma : nat) (active : bool) (value : option lit) : nat :=
  if active then gamma - option_lit_code value else 1.

Fixpoint product_slots
    (n : nat) (active : nat -> bool) (value_at : nat -> option lit)
    (gamma : nat) : nat :=
  match n with
  | 0 => 1
  | S k =>
      product_slots k active value_at gamma *
        fingerprint_term gamma (active k) (value_at k)
  end.

Definition slot_is_left_pivot (row : ResolutionAirRow) (slot : nat) : bool :=
  option_lit_eqb (nth_error (air_left_clause row) slot) (pivot_pos (air_pivot row)).

Definition slot_is_right_neg_pivot (row : ResolutionAirRow) (slot : nat) : bool :=
  option_lit_eqb (nth_error (air_right_clause row) slot) (pivot_neg (air_pivot row)).

Definition slot_is_left_source (row : ResolutionAirRow) (slot : nat) : bool :=
  match nth_error (air_left_clause row) slot with
  | None => false
  | Some l => if lit_eq_dec l (pivot_pos (air_pivot row)) then false else true
  end.

Definition slot_is_right_source (row : ResolutionAirRow) (slot : nat) : bool :=
  match nth_error (air_right_clause row) slot with
  | None => false
  | Some l => if lit_eq_dec l (pivot_neg (air_pivot row)) then false else true
  end.

Definition slot_is_left_selected (row : ResolutionAirRow) (slot : nat) : bool :=
  nth slot (air_left_keep_flags row) false.

Definition slot_is_right_selected (row : ResolutionAirRow) (slot : nat) : bool :=
  nth slot (air_right_keep_flags row) false.

Definition trace_row_extracts_air
    (width : nat) (trace : resolution_trace_matrix)
    (row_index : nat) (row : ResolutionAirRow) : Prop :=
  trace_bool trace row_index RES_IS_SEMANTIC_COL (air_is_semantic row) /\
  trace_bool trace row_index RES_IS_DERIVED_COL (air_is_derived row) /\
  trace_nat trace row_index RES_ENTRY_ID_COL (air_entry_id row) /\
  trace_nat trace row_index RES_LEFT_ID_COL (air_left_id row) /\
  trace_nat trace row_index RES_RIGHT_ID_COL (air_right_id row) /\
  trace_nat trace row_index RES_PIVOT_COL (air_pivot row) /\
  trace_clause_block
    trace row_index (res_current_lit_col 0) width (air_current_clause row) /\
  trace_clause_block
    trace row_index (res_left_lit_col width 0) width (air_left_clause row) /\
  trace_clause_block
    trace row_index (res_right_lit_col width 0) width (air_right_clause row) /\
  trace_flag_block
    trace row_index (res_left_keep_base width) width (air_left_keep_flags row) /\
  trace_flag_block
    trace row_index (res_right_keep_base width) width (air_right_keep_flags row).

Definition trace_header_aux_columns
    (width : nat) (trace : resolution_trace_matrix)
    (row_index : nat) (row : ResolutionAirRow) : Prop :=
  trace_bool trace row_index RES_IS_TABLE_COL false /\
  trace_bool trace row_index RES_IS_QUERY_COL false /\
  exists pivot_inv commit_acc_a commit_acc_b clause_mult
      left_id_inv right_id_inv left_gap_inv right_gap_inv,
    trace_nat trace row_index RES_PIVOT_INV_COL pivot_inv /\
    trace_nat trace row_index RES_COMMIT_ACC_A_COL commit_acc_a /\
    trace_nat trace row_index RES_COMMIT_ACC_B_COL commit_acc_b /\
    trace_nat trace row_index RES_CLAUSE_MULT_COL clause_mult /\
    trace_nat trace row_index RES_LEFT_ID_INV_COL left_id_inv /\
    trace_nat trace row_index RES_RIGHT_ID_INV_COL right_id_inv /\
    trace_nat trace row_index RES_LEFT_GAP_INV_COL left_gap_inv /\
    trace_nat trace row_index RES_RIGHT_GAP_INV_COL right_gap_inv /\
    trace_nat_block
      trace row_index (res_pivot_delta_base width) RES_RANGE_LIMBS [0; 0] /\
    trace_nat_block
      trace row_index
      (res_left_gap_base width)
      RES_RANGE_LIMBS
      [air_entry_id row - air_left_id row; 0] /\
    trace_nat_block
      trace row_index
      (res_right_gap_base width)
      RES_RANGE_LIMBS
      [air_entry_id row - air_right_id row; 0].

Definition trace_literal_aux_columns
    (width : nat) (trace : resolution_trace_matrix)
    (row_index clause_block : nat) (c : clause) : Prop :=
  forall slot,
    slot < width ->
    trace_bool
      trace
      row_index
      (res_literal_aux_base width clause_block slot)
      (option_lit_is_zero (nth_error c slot)) /\
    exists inv,
      trace_nat
        trace
        row_index
        (res_literal_aux_base width clause_block slot + 1)
        inv.

Definition trace_pivot_flag_columns
    (width : nat) (trace : resolution_trace_matrix)
    (row_index : nat) (row : ResolutionAirRow) : Prop :=
  forall slot,
    slot < width ->
    trace_bool
      trace row_index (res_left_pivot_eq_base width + slot)
      (slot_is_left_pivot row slot) /\
    (exists inv,
      trace_nat trace row_index (res_left_pivot_inv_base width + slot) inv) /\
    trace_bool
      trace row_index (res_right_neg_pivot_eq_base width + slot)
      (slot_is_right_neg_pivot row slot) /\
    exists inv,
      trace_nat trace row_index (res_right_neg_pivot_inv_base width + slot) inv.

Definition trace_count_product_columns
    (width : nat) (trace : resolution_trace_matrix)
    (row_index : nat) (row : ResolutionAirRow) : Prop :=
  forall slot,
    slot < width ->
    trace_nat
      trace row_index (res_left_source_count_base width + slot)
      (count_slots (S slot) (slot_is_left_source row)) /\
    trace_nat
      trace row_index (res_left_selected_count_base width + slot)
      (count_slots (S slot) (slot_is_left_selected row)) /\
    trace_nat
      trace row_index (res_right_source_count_base width + slot)
      (count_slots (S slot) (slot_is_right_source row)) /\
    trace_nat
      trace row_index (res_right_selected_count_base width + slot)
      (count_slots (S slot) (slot_is_right_selected row)) /\
    trace_nat
      trace row_index (res_left_source_prod_a_base width + slot)
      (product_slots
        (S slot)
        (slot_is_left_source row)
        (fun i => nth_error (air_left_clause row) i)
        RES_FP_GAMMA_A) /\
    trace_nat
      trace row_index (res_left_source_prod_b_base width + slot)
      (product_slots
        (S slot)
        (slot_is_left_source row)
        (fun i => nth_error (air_left_clause row) i)
        RES_FP_GAMMA_B) /\
    trace_nat
      trace row_index (res_left_selected_prod_a_base width + slot)
      (product_slots
        (S slot)
        (slot_is_left_selected row)
        (fun i => nth_error (air_current_clause row) i)
        RES_FP_GAMMA_A) /\
    trace_nat
      trace row_index (res_left_selected_prod_b_base width + slot)
      (product_slots
        (S slot)
        (slot_is_left_selected row)
        (fun i => nth_error (air_current_clause row) i)
        RES_FP_GAMMA_B) /\
    trace_nat
      trace row_index (res_right_source_prod_a_base width + slot)
      (product_slots
        (S slot)
        (slot_is_right_source row)
        (fun i => nth_error (air_right_clause row) i)
        RES_FP_GAMMA_A) /\
    trace_nat
      trace row_index (res_right_source_prod_b_base width + slot)
      (product_slots
        (S slot)
        (slot_is_right_source row)
        (fun i => nth_error (air_right_clause row) i)
        RES_FP_GAMMA_B) /\
    trace_nat
      trace row_index (res_right_selected_prod_a_base width + slot)
      (product_slots
        (S slot)
        (slot_is_right_selected row)
        (fun i => nth_error (air_current_clause row) i)
        RES_FP_GAMMA_A) /\
    trace_nat
      trace row_index (res_right_selected_prod_b_base width + slot)
      (product_slots
        (S slot)
        (slot_is_right_selected row)
        (fun i => nth_error (air_current_clause row) i)
        RES_FP_GAMMA_B).

Definition air_selected_by_flags
    (c : clause) (flags : list bool) (l : lit) : Prop :=
  exists slot,
    nth_error c slot = Some l /\
    nth_error flags slot = Some true.

Definition air_left_source (row : ResolutionAirRow) (l : lit) : Prop :=
  In l (air_left_clause row) /\ l <> pivot_pos (air_pivot row).

Definition air_right_source (row : ResolutionAirRow) (l : lit) : Prop :=
  In l (air_right_clause row) /\ l <> pivot_neg (air_pivot row).

Definition resolution_air_row_constraints (row : ResolutionAirRow) : Prop :=
  air_is_semantic row = true /\
  air_is_derived row = true /\
  air_entry_id row > air_left_id row /\
  air_entry_id row > air_right_id row /\
  air_left_id row > 0 /\
  air_right_id row > 0 /\
  In (pivot_pos (air_pivot row)) (air_left_clause row) /\
  In (pivot_neg (air_pivot row)) (air_right_clause row) /\
  (forall l,
      air_selected_by_flags (air_current_clause row) (air_left_keep_flags row) l <->
        air_left_source row l) /\
  (forall l,
      air_selected_by_flags (air_current_clause row) (air_right_keep_flags row) l <->
        air_right_source row l) /\
  (forall l,
      In l (air_current_clause row) <->
        air_selected_by_flags (air_current_clause row) (air_left_keep_flags row) l \/
        air_selected_by_flags (air_current_clause row) (air_right_keep_flags row) l).

Definition trace_resolution_logic_constraints
    (width : nat) (row : ResolutionAirRow) : Prop :=
  length (air_current_clause row) <= width /\
  length (air_left_clause row) <= width /\
  length (air_right_clause row) <= width /\
  air_is_semantic row = true /\
  air_is_derived row = true /\
  air_entry_id row > air_left_id row /\
  air_entry_id row > air_right_id row /\
  air_left_id row > 0 /\
  air_right_id row > 0 /\
  In (pivot_pos (air_pivot row)) (air_left_clause row) /\
  In (pivot_neg (air_pivot row)) (air_right_clause row) /\
  (forall l,
      air_selected_by_flags (air_current_clause row) (air_left_keep_flags row) l <->
        air_left_source row l) /\
  (forall l,
      air_selected_by_flags (air_current_clause row) (air_right_keep_flags row) l <->
        air_right_source row l) /\
  (forall l,
      In l (air_current_clause row) <->
        air_selected_by_flags (air_current_clause row) (air_left_keep_flags row) l \/
        air_selected_by_flags (air_current_clause row) (air_right_keep_flags row) l).

Definition resolution_trace_row_constraints
    (width : nat) (trace : resolution_trace_matrix)
    (row_index : nat) (row : ResolutionAirRow) : Prop :=
  trace_header_aux_columns width trace row_index row /\
  trace_literal_aux_columns width trace row_index 0 (air_current_clause row) /\
  trace_literal_aux_columns width trace row_index 1 (air_left_clause row) /\
  trace_literal_aux_columns width trace row_index 2 (air_right_clause row) /\
  trace_pivot_flag_columns width trace row_index row /\
  trace_count_product_columns width trace row_index row /\
  trace_resolution_logic_constraints width row.

Theorem resolution_trace_row_constraints_sound :
  forall width trace row_index row,
    resolution_trace_row_constraints width trace row_index row ->
    resolution_air_row_constraints row.
Proof.
  intros width trace row_index row Htrace.
  unfold resolution_trace_row_constraints in Htrace.
  destruct Htrace as [_ [_ [_ [_ [_ [_ Hlogic]]]]]].
  unfold trace_resolution_logic_constraints in Hlogic.
  destruct Hlogic as [_ [_ [_ Hrow]]].
  exact Hrow.
Qed.

Theorem resolution_air_row_sound :
  forall row,
    resolution_air_row_constraints row ->
    resolves
      (air_left_clause row)
      (air_right_clause row)
      (air_pivot row)
      (air_current_clause row).
Proof.
  intros row Hrow.
  destruct Hrow as [_ [_ [_ [_ [_ [_ [Hleft_pivot [Hright_pivot
    [Hleft_flags [Hright_flags Hcurrent]]]]]]]]]].
  split; [exact Hleft_pivot|].
  split; [exact Hright_pivot|].
  intro lit0.
  rewrite Hcurrent, Hleft_flags, Hright_flags.
  unfold oriented_resolution_member, air_left_source, air_right_source.
  reflexivity.
Qed.

Definition resolution_air_row_for_step
    (step : ResolutionStep) (row : ResolutionAirRow) : Prop :=
  air_is_derived row = true /\
  air_left_id row = left_parent step /\
  air_right_id row = right_parent step /\
  air_pivot row = pivot_var step /\
  air_current_clause row = step_resolvent step.

Fixpoint resolution_air_steps_valid
    (known : list clause) (steps : list ResolutionStep) (rows : list ResolutionAirRow) : Prop :=
  match steps, rows with
  | [], _ => True
  | _ :: _, [] => False
  | step :: rest, row :: row_rest =>
      resolution_air_row_for_step step row /\
      resolution_air_row_constraints row /\
      clause_by_id known (left_parent step) (air_left_clause row) /\
      clause_by_id known (right_parent step) (air_right_clause row) /\
      resolution_air_steps_valid (known ++ [step_resolvent step]) rest row_rest
  end.

Theorem resolution_air_steps_sound :
  forall known steps rows,
    resolution_air_steps_valid known steps rows ->
    resolution_steps_valid known steps.
Proof.
  intros known steps.
  revert known.
  induction steps as [| step rest IH]; intros known rows Hair.
  - simpl. exact I.
  - destruct rows as [| row row_rest]; [contradiction|].
    simpl in Hair.
    destruct Hair as [Hfor_step [Hrow [Hleft_id [Hright_id Hrest]]]].
    destruct Hfor_step as [_ [Hleft_eq [Hright_eq [Hpivot_eq Hres_eq]]]].
    exists (air_left_clause row), (air_right_clause row).
    split.
    + exact Hleft_id.
    + split.
      * exact Hright_id.
      * split.
        -- rewrite <- Hpivot_eq, <- Hres_eq.
           apply resolution_air_row_sound. exact Hrow.
        -- apply (IH (known ++ [step_resolvent step]) row_rest).
           exact Hrest.
Qed.

Definition resolution_trace_matrix_step_constraints
    (known : list clause)
    (row_index width : nat)
    (trace : resolution_trace_matrix)
    (step : ResolutionStep) : Prop :=
  exists row,
    trace_row_extracts_air width trace row_index row /\
    resolution_air_row_for_step step row /\
    resolution_trace_row_constraints width trace row_index row /\
    clause_by_id known (left_parent step) (air_left_clause row) /\
    clause_by_id known (right_parent step) (air_right_clause row).

Fixpoint resolution_trace_matrix_steps_valid
    (known : list clause)
    (row_index width : nat)
    (trace : resolution_trace_matrix)
    (steps : list ResolutionStep) : Prop :=
  match steps with
  | [] => True
  | step :: rest =>
      resolution_trace_matrix_step_constraints known row_index width trace step /\
      resolution_trace_matrix_steps_valid
        (known ++ [step_resolvent step]) (S row_index) width trace rest
  end.

Fixpoint resolution_trace_matrix_steps_valid_with_rows
    (known : list clause)
    (row_index width : nat)
    (trace : resolution_trace_matrix)
    (steps : list ResolutionStep)
    (rows : list ResolutionAirRow) : Prop :=
  match steps, rows with
  | [], _ => True
  | _ :: _, [] => False
  | step :: rest, row :: row_rest =>
      trace_row_extracts_air width trace row_index row /\
      resolution_air_row_for_step step row /\
      resolution_trace_row_constraints width trace row_index row /\
      clause_by_id known (left_parent step) (air_left_clause row) /\
      clause_by_id known (right_parent step) (air_right_clause row) /\
      resolution_trace_matrix_steps_valid_with_rows
        (known ++ [step_resolvent step]) (S row_index) width trace rest row_rest
  end.

Theorem resolution_trace_matrix_steps_pick_rows :
  forall known steps row_index width trace,
    resolution_trace_matrix_steps_valid known row_index width trace steps ->
    exists rows,
      resolution_trace_matrix_steps_valid_with_rows
        known row_index width trace steps rows.
Proof.
  intros known steps.
  revert known.
  induction steps as [| step rest IH]; intros known row_index width trace Hmatrix.
  - exists []. exact I.
  - simpl in Hmatrix.
    destruct Hmatrix as [[row Hstep] Hrest].
    destruct (IH (known ++ [step_resolvent step]) (S row_index) width trace Hrest)
      as [rows Hrows].
    exists (row :: rows).
    simpl.
    destruct Hstep as [Hextract [Hfor_step [Htrace_row [Hleft_id Hright_id]]]].
    split; [exact Hextract|].
    split; [exact Hfor_step|].
    split; [exact Htrace_row|].
    split; [exact Hleft_id|].
    split; [exact Hright_id|].
    exact Hrows.
Qed.

Theorem resolution_trace_matrix_steps_valid_with_rows_air_sound :
  forall known steps rows row_index width trace,
    resolution_trace_matrix_steps_valid_with_rows
      known row_index width trace steps rows ->
    resolution_air_steps_valid known steps rows.
Proof.
  intros known steps.
  revert known.
  induction steps as [| step rest IH]; intros known rows row_index width trace.
  - simpl. exact (fun _ => I).
  - destruct rows as [| row row_rest].
    + simpl. intro H. contradiction.
    + simpl.
      intros [_ [Hfor_step [Htrace_row [Hleft_id [Hright_id Hrest]]]]].
      split; [exact Hfor_step|].
      split.
      * apply resolution_trace_row_constraints_sound with
          (width := width) (trace := trace) (row_index := row_index).
        exact Htrace_row.
      * split; [exact Hleft_id|].
        split; [exact Hright_id|].
        apply (IH (known ++ [step_resolvent step])
          row_rest (S row_index) width trace).
        exact Hrest.
Qed.

Theorem resolution_trace_matrix_steps_air_sound :
  forall known steps row_index width trace,
    resolution_trace_matrix_steps_valid known row_index width trace steps ->
    exists rows, resolution_air_steps_valid known steps rows.
Proof.
  intros known steps row_index width trace Hmatrix.
  destruct (resolution_trace_matrix_steps_pick_rows
    known steps row_index width trace Hmatrix) as [rows Hrows].
  exists rows.
  apply resolution_trace_matrix_steps_valid_with_rows_air_sound with
    (row_index := row_index) (width := width) (trace := trace).
  exact Hrows.
Qed.

Theorem resolution_trace_matrix_steps_sound :
  forall known steps row_index width trace,
    resolution_trace_matrix_steps_valid known row_index width trace steps ->
    resolution_steps_valid known steps.
Proof.
  intros known steps row_index width trace Hmatrix.
  destruct (resolution_trace_matrix_steps_air_sound
    known steps row_index width trace Hmatrix) as [rows Hair].
  apply resolution_air_steps_sound with (rows := rows).
  exact Hair.
Qed.

Record UnsatCircuitWitness := {
  unsat_steps : list ResolutionStep;
  clause_matrix : matrix lit;
  resolution_trace_width_bound : nat;
  resolution_trace : resolution_trace_matrix
}.

Definition row_encodes_clause (m : matrix lit) (row : nat) (c : clause) : Prop :=
  forall col, m row col = nth_error c col.

Definition resolution_matrix_encodes
    (f : cnf) (steps : list ResolutionStep) (m : matrix lit) : Prop :=
  (forall row c,
      nth_error f row = Some c ->
      row_encodes_clause m row c) /\
  (forall k step,
      nth_error steps k = Some step ->
      row_encodes_clause m (length f + k) (step_resolvent step)).

Definition unsat_circuit_constraints (f : cnf) (w : UnsatCircuitWitness) : Prop :=
  resolution_matrix_encodes f (unsat_steps w) (clause_matrix w) /\
  resolution_trace_matrix_steps_valid
    f
    (length f)
    (resolution_trace_width_bound w)
    (resolution_trace w)
    (unsat_steps w) /\
  final_step_empty (unsat_steps w).

Theorem unsat_constraints_sound_refutation :
  forall f w,
    unsat_circuit_constraints f w ->
    resolution_refutation f (unsat_steps w).
Proof.
  intros f w [_ [Hsteps Hempty]].
  split.
  - apply resolution_trace_matrix_steps_sound with
      (row_index := length f)
      (width := resolution_trace_width_bound w)
      (trace := resolution_trace w).
    exact Hsteps.
  - exact Hempty.
Qed.

Lemma nth_error_some_in :
  forall (A : Type) (xs : list A) (n : nat) (x : A),
    nth_error xs n = Some x -> In x xs.
Proof.
  intros A xs n x Hnth.
  apply nth_error_In with (n := n). exact Hnth.
Qed.

Lemma lit_eval_pivot_contradiction :
  forall a p,
    lit_eval a (pivot_pos p) = true ->
    lit_eval a (pivot_neg p) = true ->
    False.
Proof.
  intros a p Hpos Hneg.
  unfold lit_eval, pivot_pos, pivot_neg in *.
  rewrite Hpos in Hneg. discriminate.
Qed.

Lemma resolve_preserves_clause_holds :
  forall a left right pivot resolvent,
    resolves left right pivot resolvent ->
    clause_holds a left ->
    clause_holds a right ->
    clause_holds a resolvent.
Proof.
  intros a left right pivot resolvent Hres Hleft Hright.
  destruct Hres as [Hleft_pivot [Hright_pivot Hmembers]].
  destruct Hleft as [jl [ll [Hll_nth Hll_true]]].
  destruct Hright as [jr [lr [Hlr_nth Hlr_true]]].
  pose proof (@nth_error_some_in lit left jl ll Hll_nth) as Hll_in.
  pose proof (@nth_error_some_in lit right jr lr Hlr_nth) as Hlr_in.
  destruct (lit_eq_dec ll (pivot_pos pivot)) as [Hll_pivot | Hll_not_pivot].
  - subst ll.
    destruct (lit_eq_dec lr (pivot_neg pivot)) as [Hlr_pivot | Hlr_not_neg].
    + subst lr.
      exfalso. eapply lit_eval_pivot_contradiction; eauto.
    +
      assert (Hin_res : In lr resolvent).
      { apply (proj2 (Hmembers lr)).
        right. split; assumption. }
      destruct (@in_nth_error_exists lit lr resolvent Hin_res) as [j Hj].
      exists j, lr. split; assumption.
  - assert (Hin_res : In ll resolvent).
    { apply (proj2 (Hmembers ll)).
      left. split; assumption. }
    destruct (@in_nth_error_exists lit ll resolvent Hin_res) as [j Hj].
    exists j, ll. split; assumption.
Qed.

Definition derived_resolvents (steps : list ResolutionStep) : list clause :=
  map step_resolvent steps.

Lemma all_clauses_hold_app :
  forall a xs ys,
    all_clauses_hold a (xs ++ ys) ->
    all_clauses_hold a xs /\ all_clauses_hold a ys.
Proof.
  intros a xs ys Hall.
  split; intros c Hin; apply Hall; apply in_or_app; auto.
Qed.

Lemma all_clauses_hold_extend :
  forall a known c,
    all_clauses_hold a known ->
    clause_holds a c ->
    all_clauses_hold a (known ++ [c]).
Proof.
  intros a known c Hknown Hc d Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - apply Hknown. exact Hin.
  - simpl in Hin. destruct Hin as [Heq | []].
    subst. exact Hc.
Qed.

Lemma resolution_steps_valid_sound :
  forall steps known a,
    resolution_steps_valid known steps ->
    all_clauses_hold a known ->
    all_clauses_hold a (known ++ derived_resolvents steps).
Proof.
  induction steps as [| step rest IH]; intros known a Hvalid Hknown.
  - simpl. rewrite app_nil_r. exact Hknown.
  - simpl in Hvalid.
    destruct Hvalid as [left [right [Hleft_id [Hright_id [Hres Hrest]]]]].
    pose proof (clause_by_id_in Hleft_id) as Hleft_in.
    pose proof (clause_by_id_in Hright_id) as Hright_in.
    pose proof (Hknown left Hleft_in) as Hleft_holds.
    pose proof (Hknown right Hright_in) as Hright_holds.
    pose proof (resolve_preserves_clause_holds Hres Hleft_holds Hright_holds)
      as Hres_holds.
    specialize (IH (known ++ [step_resolvent step]) a Hrest).
    specialize (IH (all_clauses_hold_extend Hknown Hres_holds)).
    intros c Hin.
    simpl in Hin.
    rewrite <- app_assoc in IH.
    apply IH.
    exact Hin.
Qed.

Lemma empty_clause_not_holds :
  forall a, ~ clause_holds a [].
Proof.
  intros a [j [l [Hnth _]]].
  destruct j; discriminate.
Qed.

Lemma empty_resolvent_in_derived :
  forall steps,
    final_step_empty steps ->
    In [] (derived_resolvents steps).
Proof.
  intros steps [prefix [step [Hsteps Hempty]]].
  subst steps. unfold derived_resolvents. rewrite map_app.
  induction prefix as [| p ps IH].
  - simpl. left. exact Hempty.
  - simpl. right. exact IH.
Qed.

Theorem resolution_refutation_sound_unsat :
  forall f steps a,
    resolution_refutation f steps ->
    cnf_holds a f ->
    False.
Proof.
  intros f steps a [Hvalid Hempty] Hcnf.
  pose proof
    (@resolution_steps_valid_sound steps f a Hvalid (cnf_holds_all_clauses_hold Hcnf))
    as Hall.
  assert (Hin_empty : In [] (f ++ derived_resolvents steps)).
  { apply in_or_app. right. apply empty_resolvent_in_derived. exact Hempty. }
  specialize (Hall [] Hin_empty).
  apply (@empty_clause_not_holds a). exact Hall.
Qed.

Theorem unsat_constraints_sound_unsat :
  forall f w a,
    unsat_circuit_constraints f w ->
    cnf_holds a f ->
    False.
Proof.
  intros f w a Hconstraints Hcnf.
  apply (resolution_refutation_sound_unsat (f := f) (steps := unsat_steps w) (a := a)).
  - apply unsat_constraints_sound_refutation. exact Hconstraints.
  - exact Hcnf.
Qed.

End CircuitSoundness.
