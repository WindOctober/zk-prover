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

Definition row_encodes_clause (m : matrix lit) (row : nat) (c : clause) : Prop :=
  forall col, m row col = nth_error c col.

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

Definition selected_count
    (n : nat) (active : nat -> bool) (value_at : nat -> option lit)
    (target : lit) : nat :=
  count_slots n
    (fun slot =>
      if active slot then option_lit_eqb (value_at slot) target else false).

Definition fingerprint_product := lit -> nat.

Definition fingerprint_slots
    (n : nat) (active : nat -> bool) (value_at : nat -> option lit)
    : fingerprint_product :=
  fun l => selected_count n active value_at l.

Definition same_fingerprint_product
    (left right : fingerprint_product) : Prop :=
  forall l, left l = right l.

Definition trace_count_product_final_constraints
    (width : nat) (row : ResolutionAirRow) : Prop :=
  width > 0 /\
  count_slots width (slot_is_left_source row) =
    count_slots width (slot_is_left_selected row) /\
  count_slots width (slot_is_right_source row) =
    count_slots width (slot_is_right_selected row) /\
  same_fingerprint_product
    (fingerprint_slots
      width
      (slot_is_left_source row)
      (fun slot => nth_error (air_left_clause row) slot))
    (fingerprint_slots
      width
      (slot_is_left_selected row)
      (fun slot => nth_error (air_current_clause row) slot)) /\
  same_fingerprint_product
    (fingerprint_slots
      width
      (slot_is_right_source row)
      (fun slot => nth_error (air_right_clause row) slot))
    (fingerprint_slots
      width
      (slot_is_right_selected row)
      (fun slot => nth_error (air_current_clause row) slot)).

Definition trace_current_clause_selection_constraints (row : ResolutionAirRow) : Prop :=
  forall slot l,
    nth_error (air_current_clause row) slot = Some l ->
    nth_error (air_left_keep_flags row) slot = Some true \/
    nth_error (air_right_keep_flags row) slot = Some true.

Definition trace_pivot_count_constraints (width : nat) (row : ResolutionAirRow) : Prop :=
  count_slots width (slot_is_left_pivot row) = 1 /\
  count_slots width (slot_is_right_neg_pivot row) = 1.

Definition resolution_clause_bus_constraints
    (m : matrix lit) (row : ResolutionAirRow) : Prop :=
  row_encodes_clause m (air_entry_id row - 1) (air_current_clause row) /\
  row_encodes_clause m (air_left_id row - 1) (air_left_clause row) /\
  row_encodes_clause m (air_right_id row - 1) (air_right_clause row).

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

Lemma trace_current_clause_selection_constraints_sound :
  forall row l,
    trace_current_clause_selection_constraints row ->
    In l (air_current_clause row) <->
      air_selected_by_flags (air_current_clause row) (air_left_keep_flags row) l \/
      air_selected_by_flags (air_current_clause row) (air_right_keep_flags row) l.
Proof.
  intros row l Hselected.
  split.
  - intro Hin.
    destruct (@in_nth_error_exists lit l (air_current_clause row) Hin) as [slot Hnth].
    specialize (Hselected slot l Hnth) as [Hleft | Hright].
    + left. exists slot. split; [exact Hnth| exact Hleft].
    + right. exists slot. split; [exact Hnth| exact Hright].
  - intros [[slot [Hnth _]] | [slot [Hnth _]]];
      apply nth_error_In with (n := slot); exact Hnth.
Qed.

Lemma count_slots_true_positive :
  forall n active slot,
    slot < n ->
    active slot = true ->
    count_slots n active > 0.
Proof.
  induction n as [| n IH]; intros active slot Hlt Hactive.
  - lia.
  - simpl.
    destruct (Nat.eq_dec slot n) as [Heq | Hneq].
    + subst slot. rewrite Hactive. unfold bool_to_nat. lia.
    + assert (slot < n) as Hslot_lt by lia.
      specialize (IH active slot Hslot_lt Hactive).
      destruct (active n); simpl; lia.
Qed.

Lemma count_slots_positive_exists :
  forall n active,
    count_slots n active > 0 ->
    exists slot,
      slot < n /\ active slot = true.
Proof.
  induction n as [| n IH]; intros active Hcount.
  - simpl in Hcount. lia.
  - simpl in Hcount.
    destruct (active n) eqn:Hactive.
    + exists n. split; [lia| exact Hactive].
    + simpl in Hcount.
      assert (count_slots n active > 0) by lia.
      destruct (IH active H) as [slot [Hslot Hslot_active]].
      exists slot. split; [lia| exact Hslot_active].
Qed.

Lemma option_lit_eqb_true :
  forall value l,
    option_lit_eqb value l = true ->
    value = Some l.
Proof.
  intros value l Hflag.
  unfold option_lit_eqb in Hflag.
  destruct value as [x |]; [| discriminate].
  destruct (lit_eq_dec x l) as [Heq | Hneq].
  - subst. reflexivity.
  - discriminate.
Qed.

Lemma nth_error_true_nth :
  forall flags slot,
    nth_error flags slot = Some true ->
    nth slot flags false = true.
Proof.
  induction flags as [| flag flags_tail IH]; intros [| slot] Hnth;
    simpl in *; try discriminate.
  - inversion Hnth. reflexivity.
  - apply IH. exact Hnth.
Qed.

Lemma nth_true_nth_error :
  forall flags slot,
    nth slot flags false = true ->
    nth_error flags slot = Some true.
Proof.
  induction flags as [| flag flags_tail IH]; intros [| slot] Hnth;
    simpl in *; try discriminate.
  - destruct flag; [reflexivity| discriminate].
  - apply IH. exact Hnth.
Qed.

Lemma selected_count_active_value_sound :
  forall n active value_at l,
    selected_count n active value_at l > 0 <->
      exists slot,
        slot < n /\
        active slot = true /\
        value_at slot = Some l.
Proof.
  intros n active value_at l.
  unfold selected_count.
  split.
  - intro Hcount.
    destruct (count_slots_positive_exists _ _ Hcount)
      as [slot [Hslot Hactive_value]].
    exists slot. split; [exact Hslot|].
    destruct (active slot) eqn:Hactive; [| discriminate].
    split; [reflexivity|].
    apply option_lit_eqb_true. exact Hactive_value.
  - intros [slot [Hslot [Hactive Hvalue]]].
    apply count_slots_true_positive with (slot := slot).
    + exact Hslot.
    + rewrite Hactive, Hvalue.
      unfold option_lit_eqb.
      destruct (lit_eq_dec l l) as [_ | Hneq]; [reflexivity| contradiction].
Qed.

Lemma air_selected_by_flags_selected_count :
  forall width c flags l,
    length c <= width ->
    (air_selected_by_flags c flags l <->
      selected_count
        width
        (fun slot => nth slot flags false)
        (fun slot => nth_error c slot)
        l > 0).
Proof.
  intros width c flags l Hlen.
  split.
  - intros [slot [Hnth Hflag]].
    rewrite selected_count_active_value_sound.
    exists slot. split.
    + assert (slot < length c) as Hslot_len.
      { apply nth_error_Some. rewrite Hnth. discriminate. }
      lia.
    + split.
      * apply nth_error_true_nth. exact Hflag.
      * exact Hnth.
  - intro Hcount.
    rewrite selected_count_active_value_sound in Hcount.
    destruct Hcount as [slot [_ [Hflag Hnth]]].
    exists slot. split; [exact Hnth|].
    apply nth_true_nth_error. exact Hflag.
Qed.

Lemma air_left_source_selected_count :
  forall width row l,
    length (air_left_clause row) <= width ->
    (air_left_source row l <->
      selected_count
        width
        (slot_is_left_source row)
        (fun slot => nth_error (air_left_clause row) slot)
        l > 0).
Proof.
  intros width row l Hlen.
  split.
  - intros [Hin Hnot_pivot].
    destruct (@in_nth_error_exists lit l (air_left_clause row) Hin)
      as [slot Hnth].
    rewrite selected_count_active_value_sound.
    exists slot. split.
    + assert (slot < length (air_left_clause row)) as Hslot_len.
      { apply nth_error_Some. rewrite Hnth. discriminate. }
      lia.
    + split.
      * unfold slot_is_left_source. rewrite Hnth.
        destruct (lit_eq_dec l (pivot_pos (air_pivot row))) as [Heq | Hneq].
        -- contradiction.
        -- reflexivity.
      * exact Hnth.
  - intro Hcount.
    rewrite selected_count_active_value_sound in Hcount.
    destruct Hcount as [slot [_ [Hsource Hnth]]].
    split.
    + apply nth_error_In with (n := slot). exact Hnth.
    + unfold slot_is_left_source in Hsource.
      rewrite Hnth in Hsource.
      destruct (lit_eq_dec l (pivot_pos (air_pivot row))) as [Heq | Hneq].
      * discriminate.
      * exact Hneq.
Qed.

Lemma air_right_source_selected_count :
  forall width row l,
    length (air_right_clause row) <= width ->
    (air_right_source row l <->
      selected_count
        width
        (slot_is_right_source row)
        (fun slot => nth_error (air_right_clause row) slot)
        l > 0).
Proof.
  intros width row l Hlen.
  split.
  - intros [Hin Hnot_pivot].
    destruct (@in_nth_error_exists lit l (air_right_clause row) Hin)
      as [slot Hnth].
    rewrite selected_count_active_value_sound.
    exists slot. split.
    + assert (slot < length (air_right_clause row)) as Hslot_len.
      { apply nth_error_Some. rewrite Hnth. discriminate. }
      lia.
    + split.
      * unfold slot_is_right_source. rewrite Hnth.
        destruct (lit_eq_dec l (pivot_neg (air_pivot row))) as [Heq | Hneq].
        -- contradiction.
        -- reflexivity.
      * exact Hnth.
  - intro Hcount.
    rewrite selected_count_active_value_sound in Hcount.
    destruct Hcount as [slot [_ [Hsource Hnth]]].
    split.
    + apply nth_error_In with (n := slot). exact Hnth.
    + unfold slot_is_right_source in Hsource.
      rewrite Hnth in Hsource.
      destruct (lit_eq_dec l (pivot_neg (air_pivot row))) as [Heq | Hneq].
      * discriminate.
      * exact Hneq.
Qed.

Lemma trace_count_product_final_constraints_sources_sound :
  forall width row l,
    length (air_current_clause row) <= width ->
    length (air_left_clause row) <= width ->
    length (air_right_clause row) <= width ->
    trace_count_product_final_constraints width row ->
    (air_selected_by_flags (air_current_clause row) (air_left_keep_flags row) l <->
      air_left_source row l) /\
    (air_selected_by_flags (air_current_clause row) (air_right_keep_flags row) l <->
      air_right_source row l).
Proof.
  intros width row l Hlen_current Hlen_left Hlen_right Hfinal.
  destruct Hfinal as [_ [_ [_ [Hleft_fingerprint Hright_fingerprint]]]].
  split.
  - pose proof (@air_selected_by_flags_selected_count
      width (air_current_clause row) (air_left_keep_flags row) l Hlen_current)
      as Hselected_count.
    pose proof (@air_left_source_selected_count width row l Hlen_left)
      as Hsource_count.
    rewrite Hselected_count, Hsource_count.
    unfold same_fingerprint_product, fingerprint_slots in Hleft_fingerprint.
    rewrite (Hleft_fingerprint l). reflexivity.
  - pose proof (@air_selected_by_flags_selected_count
      width (air_current_clause row) (air_right_keep_flags row) l Hlen_current)
      as Hselected_count.
    pose proof (@air_right_source_selected_count width row l Hlen_right)
      as Hsource_count.
    rewrite Hselected_count, Hsource_count.
    unfold same_fingerprint_product, fingerprint_slots in Hright_fingerprint.
    rewrite (Hright_fingerprint l). reflexivity.
Qed.

Lemma slot_is_left_pivot_sound :
  forall row slot,
    slot_is_left_pivot row slot = true ->
    nth_error (air_left_clause row) slot = Some (pivot_pos (air_pivot row)).
Proof.
  intros row slot Hflag.
  unfold slot_is_left_pivot, option_lit_eqb in Hflag.
  destruct (nth_error (air_left_clause row) slot) as [l |] eqn:Hnth;
    [| discriminate].
  destruct (lit_eq_dec l (pivot_pos (air_pivot row))) as [Heq | Hneq];
    [subst; reflexivity| discriminate].
Qed.

Lemma slot_is_right_neg_pivot_sound :
  forall row slot,
    slot_is_right_neg_pivot row slot = true ->
    nth_error (air_right_clause row) slot = Some (pivot_neg (air_pivot row)).
Proof.
  intros row slot Hflag.
  unfold slot_is_right_neg_pivot, option_lit_eqb in Hflag.
  destruct (nth_error (air_right_clause row) slot) as [l |] eqn:Hnth;
    [| discriminate].
  destruct (lit_eq_dec l (pivot_neg (air_pivot row))) as [Heq | Hneq];
    [subst; reflexivity| discriminate].
Qed.

Lemma trace_pivot_count_constraints_sound :
  forall width row,
    trace_pivot_count_constraints width row ->
    In (pivot_pos (air_pivot row)) (air_left_clause row) /\
    In (pivot_neg (air_pivot row)) (air_right_clause row).
Proof.
  intros width row [Hleft_count Hright_count].
  split.
  - assert (count_slots width (slot_is_left_pivot row) > 0) by lia.
    destruct (count_slots_positive_exists width (slot_is_left_pivot row) H)
      as [slot [_ Hflag]].
    apply nth_error_In with (n := slot).
    apply slot_is_left_pivot_sound. exact Hflag.
  - assert (count_slots width (slot_is_right_neg_pivot row) > 0) by lia.
    destruct (count_slots_positive_exists width (slot_is_right_neg_pivot row) H)
      as [slot [_ Hflag]].
    apply nth_error_In with (n := slot).
    apply slot_is_right_neg_pivot_sound. exact Hflag.
Qed.

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
  trace_pivot_count_constraints width row /\
  trace_count_product_final_constraints width row /\
  trace_current_clause_selection_constraints row.

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
  destruct Hlogic as [Hlen_current Hlogic].
  destruct Hlogic as [Hlen_left Hlogic].
  destruct Hlogic as [Hlen_right Hlogic].
  destruct Hlogic as [Hsemantic Hlogic].
  destruct Hlogic as [Hderived Hlogic].
  destruct Hlogic as [Hentry_left Hlogic].
  destruct Hlogic as [Hentry_right Hlogic].
  destruct Hlogic as [Hleft_id_pos Hlogic].
  destruct Hlogic as [Hright_id_pos Hlogic].
  destruct Hlogic as [Hpivot_counts [Hcount_product_final Hcurrent_selected]].
  destruct (trace_pivot_count_constraints_sound Hpivot_counts)
    as [Hleft_pivot Hright_pivot].
  split; [exact Hsemantic|].
  split; [exact Hderived|].
  split; [exact Hentry_left|].
  split; [exact Hentry_right|].
  split; [exact Hleft_id_pos|].
  split; [exact Hright_id_pos|].
  split; [exact Hleft_pivot|].
  split; [exact Hright_pivot|].
  split.
  - intro l.
    destruct (@trace_count_product_final_constraints_sources_sound
      width row l Hlen_current Hlen_left Hlen_right Hcount_product_final)
      as [Hleft _].
    exact Hleft.
  - split.
    + intro l.
      destruct (@trace_count_product_final_constraints_sources_sound
        width row l Hlen_current Hlen_left Hlen_right Hcount_product_final)
        as [_ Hright].
      exact Hright.
    + intro l.
      apply trace_current_clause_selection_constraints_sound.
      exact Hcurrent_selected.
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

Definition matrix_rows_encode_known (m : matrix lit) (known : list clause) : Prop :=
  forall row c,
    nth_error known row = Some c ->
    row_encodes_clause m row c.

Lemma row_encodes_clause_ext :
  forall m row c1 c2,
    row_encodes_clause m row c1 ->
    row_encodes_clause m row c2 ->
    c1 = c2.
Proof.
  intros m row c1 c2 Hc1 Hc2.
  apply nth_error_ext. intro col.
  rewrite <- Hc1, <- Hc2. reflexivity.
Qed.

Lemma nth_error_exists_of_lt :
  forall (A : Type) (xs : list A) n,
    n < length xs ->
    exists x, nth_error xs n = Some x.
Proof.
  intros A xs n Hlt.
  destruct (nth_error xs n) as [x |] eqn:Hnth.
  - exists x. reflexivity.
  - apply nth_error_None in Hnth. lia.
Qed.

Lemma matrix_rows_encode_known_clause_by_id :
  forall m known id c,
    matrix_rows_encode_known m known ->
    id > 0 ->
    id <= length known ->
    row_encodes_clause m (id - 1) c ->
    clause_by_id known id c.
Proof.
  intros m known id c Hknown Hid_pos Hid_bound Hrow.
  split; [exact Hid_pos|].
  destruct (@nth_error_exists_of_lt clause known (id - 1)) as [known_c Hknown_c].
  - lia.
  - specialize (Hknown (id - 1) known_c Hknown_c) as Hknown_row.
    assert (c = known_c) as Heq.
    { apply row_encodes_clause_ext with (m := m) (row := id - 1);
        assumption. }
    subst c. exact Hknown_c.
Qed.

Lemma matrix_rows_encode_known_snoc :
  forall m known c,
    matrix_rows_encode_known m known ->
    row_encodes_clause m (length known) c ->
    matrix_rows_encode_known m (known ++ [c]).
Proof.
  intros m known c Hknown Hcurrent row c' Hnth.
  destruct (row <? length known) eqn:Hrow_lt.
  - apply Nat.ltb_lt in Hrow_lt.
    rewrite nth_error_app1 in Hnth by exact Hrow_lt.
    apply Hknown. exact Hnth.
  - apply Nat.ltb_ge in Hrow_lt.
    pose proof Hnth as Hnth_app.
    rewrite nth_error_app2 in Hnth by lia.
    destruct (row - length known) as [| extra] eqn:Hdiff.
    + inversion Hnth. subst c'.
      assert (row = length known) by lia.
      subst row. exact Hcurrent.
    + assert (row < length (known ++ [c])) as Hrow_bound.
      { apply nth_error_Some. rewrite Hnth_app. discriminate. }
      rewrite length_app in Hrow_bound. simpl in Hrow_bound. lia.
Qed.

Definition resolution_trace_matrix_step_constraints
    (m : matrix lit)
    (known : list clause)
    (row_index width : nat)
    (trace : resolution_trace_matrix)
    (step : ResolutionStep) : Prop :=
  exists row,
    trace_row_extracts_air width trace row_index row /\
    resolution_air_row_for_step step row /\
    air_entry_id row = S (length known) /\
    resolution_trace_row_constraints width trace row_index row /\
    resolution_clause_bus_constraints m row.

Fixpoint resolution_trace_matrix_steps_valid
    (m : matrix lit)
    (known : list clause)
    (row_index width : nat)
    (trace : resolution_trace_matrix)
    (steps : list ResolutionStep) : Prop :=
  match steps with
  | [] => True
  | step :: rest =>
      resolution_trace_matrix_step_constraints m known row_index width trace step /\
      resolution_trace_matrix_steps_valid
        m (known ++ [step_resolvent step]) (S row_index) width trace rest
  end.

Fixpoint resolution_trace_matrix_steps_valid_with_rows
    (m : matrix lit)
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
      air_entry_id row = S (length known) /\
      resolution_trace_row_constraints width trace row_index row /\
      resolution_clause_bus_constraints m row /\
      resolution_trace_matrix_steps_valid_with_rows
        m (known ++ [step_resolvent step]) (S row_index) width trace rest row_rest
  end.

Theorem resolution_trace_matrix_steps_pick_rows :
  forall m known steps row_index width trace,
    resolution_trace_matrix_steps_valid m known row_index width trace steps ->
    exists rows,
      resolution_trace_matrix_steps_valid_with_rows
        m known row_index width trace steps rows.
Proof.
  intros m known steps.
  revert known.
  induction steps as [| step rest IH]; intros known row_index width trace Hmatrix.
  - exists []. exact I.
  - simpl in Hmatrix.
    destruct Hmatrix as [[row Hstep] Hrest].
    destruct (IH (known ++ [step_resolvent step]) (S row_index) width trace Hrest)
      as [rows Hrows].
    exists (row :: rows).
    simpl.
    destruct Hstep as [Hextract [Hfor_step [Hentry [Htrace_row Hbus]]]].
    split; [exact Hextract|].
    split; [exact Hfor_step|].
    split; [exact Hentry|].
    split; [exact Htrace_row|].
    split; [exact Hbus|].
    exact Hrows.
Qed.

Theorem resolution_trace_matrix_steps_valid_with_rows_air_sound :
  forall m known steps rows row_index width trace,
    matrix_rows_encode_known m known ->
    resolution_trace_matrix_steps_valid_with_rows
      m known row_index width trace steps rows ->
    resolution_air_steps_valid known steps rows.
Proof.
  intros m known steps.
  revert known.
  induction steps as [| step rest IH]; intros known rows row_index width trace Hknown.
  - simpl. exact (fun _ => I).
  - destruct rows as [| row row_rest].
    + simpl. intro H. contradiction.
    + simpl.
      intros [_ [Hfor_step [Hentry [Htrace_row [Hbus Hrest]]]]].
      destruct Hbus as [Hcurrent_bus [Hleft_bus Hright_bus]].
      pose proof (resolution_trace_row_constraints_sound Htrace_row) as Hair_row.
      destruct Hair_row as [_ [_ [Hentry_left [Hentry_right
        [Hleft_id_pos [Hright_id_pos _]]]]]].
      assert (air_left_id row <= length known) as Hleft_bound by lia.
      assert (air_right_id row <= length known) as Hright_bound by lia.
      assert (clause_by_id known (left_parent step) (air_left_clause row))
        as Hleft_id.
      { destruct Hfor_step as [_ [Hleft_eq _]].
        rewrite <- Hleft_eq.
        apply matrix_rows_encode_known_clause_by_id with (m := m).
        - exact Hknown.
        - exact Hleft_id_pos.
        - exact Hleft_bound.
        - exact Hleft_bus. }
      assert (clause_by_id known (right_parent step) (air_right_clause row))
        as Hright_id.
      { destruct Hfor_step as [_ [_ [Hright_eq _]]].
        rewrite <- Hright_eq.
        apply matrix_rows_encode_known_clause_by_id with (m := m).
        - exact Hknown.
        - exact Hright_id_pos.
        - exact Hright_bound.
        - exact Hright_bus. }
      split; [exact Hfor_step|].
      split.
      * exact (resolution_trace_row_constraints_sound Htrace_row).
      * split; [exact Hleft_id|].
        split; [exact Hright_id|].
        apply (IH (known ++ [step_resolvent step])
          row_rest (S row_index) width trace).
        -- apply matrix_rows_encode_known_snoc.
           ++ exact Hknown.
           ++ destruct Hfor_step as [_ [_ [_ [_ Hcurrent_eq]]]].
              rewrite <- Hcurrent_eq.
              replace (length known) with (air_entry_id row - 1) by lia.
              exact Hcurrent_bus.
        -- exact Hrest.
Qed.

Theorem resolution_trace_matrix_steps_air_sound :
  forall m known steps row_index width trace,
    matrix_rows_encode_known m known ->
    resolution_trace_matrix_steps_valid m known row_index width trace steps ->
    exists rows, resolution_air_steps_valid known steps rows.
Proof.
  intros m known steps row_index width trace Hknown Hmatrix.
  destruct (resolution_trace_matrix_steps_pick_rows
    m known steps row_index width trace Hmatrix) as [rows Hrows].
  exists rows.
  apply resolution_trace_matrix_steps_valid_with_rows_air_sound with
    (m := m) (row_index := row_index) (width := width) (trace := trace).
  - exact Hknown.
  - exact Hrows.
Qed.

Theorem resolution_trace_matrix_steps_sound :
  forall m known steps row_index width trace,
    matrix_rows_encode_known m known ->
    resolution_trace_matrix_steps_valid m known row_index width trace steps ->
    resolution_steps_valid known steps.
Proof.
  intros m known steps row_index width trace Hknown Hmatrix.
  destruct (@resolution_trace_matrix_steps_air_sound
    m known steps row_index width trace Hknown Hmatrix) as [rows Hair].
  apply resolution_air_steps_sound with (rows := rows).
  exact Hair.
Qed.

Record UnsatCircuitWitness := {
  unsat_steps : list ResolutionStep;
  clause_matrix : matrix lit;
  resolution_trace_width_bound : nat;
  resolution_trace : resolution_trace_matrix
}.

Definition resolution_matrix_encodes
    (f : cnf) (steps : list ResolutionStep) (m : matrix lit) : Prop :=
  (forall row c,
      nth_error f row = Some c ->
      row_encodes_clause m row c) /\
  (forall k step,
      nth_error steps k = Some step ->
      row_encodes_clause m (length f + k) (step_resolvent step)).

Lemma resolution_matrix_encodes_initial_known :
  forall f steps m,
    resolution_matrix_encodes f steps m ->
    matrix_rows_encode_known m f.
Proof.
  intros f steps m [Hformula _] row c Hnth.
  apply Hformula. exact Hnth.
Qed.

Definition unsat_circuit_constraints (f : cnf) (w : UnsatCircuitWitness) : Prop :=
  resolution_matrix_encodes f (unsat_steps w) (clause_matrix w) /\
  resolution_trace_matrix_steps_valid
    (clause_matrix w)
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
  intros f w [Hmatrix [Hsteps Hempty]].
  split.
  - apply resolution_trace_matrix_steps_sound with
      (m := clause_matrix w)
      (row_index := length f)
      (width := resolution_trace_width_bound w)
      (trace := resolution_trace w).
    + apply resolution_matrix_encodes_initial_known with
        (steps := unsat_steps w).
      exact Hmatrix.
    + exact Hsteps.
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
