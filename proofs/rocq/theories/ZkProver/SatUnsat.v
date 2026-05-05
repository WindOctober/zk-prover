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

Definition pivot_pos (p : var) : lit := Pos p.
Definition pivot_neg (p : var) : lit := Neg p.

Definition resolves (left right : clause) (pivot : var) (resolvent : clause) : Prop :=
  In (pivot_pos pivot) left /\
  In (pivot_neg pivot) right /\
  ~ In (pivot_neg pivot) left /\
  ~ In (pivot_pos pivot) right /\
  forall l,
    In l resolvent <->
      (In l left \/ In l right) /\
      l <> pivot_pos pivot /\
      l <> pivot_neg pivot.

Fixpoint resolution_steps_valid (known : list clause) (steps : list ResolutionStep) : Prop :=
  match steps with
  | [] => True
  | step :: rest =>
      exists left right,
        nth_error known (left_parent step) = Some left /\
        nth_error known (right_parent step) = Some right /\
        resolves left right (pivot_var step) (step_resolvent step) /\
        resolution_steps_valid (known ++ [step_resolvent step]) rest
  end.

Definition final_step_empty (steps : list ResolutionStep) : Prop :=
  exists prefix step,
    steps = prefix ++ [step] /\
    step_resolvent step = [].

Definition resolution_refutation (f : cnf) (steps : list ResolutionStep) : Prop :=
  resolution_steps_valid f steps /\ final_step_empty steps.

Record UnsatCircuitWitness := {
  unsat_steps : list ResolutionStep;
  clause_matrix : matrix lit
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
  resolution_steps_valid f (unsat_steps w) /\
  final_step_empty (unsat_steps w).

Theorem unsat_constraints_sound_refutation :
  forall f w,
    unsat_circuit_constraints f w ->
    resolution_refutation f (unsat_steps w).
Proof.
  intros f w [_ [Hsteps Hempty]].
  split; assumption.
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
  destruct Hres as [Hleft_pivot [Hright_pivot [Hleft_clean [Hright_clean Hmembers]]]].
  destruct Hleft as [jl [ll [Hll_nth Hll_true]]].
  destruct Hright as [jr [lr [Hlr_nth Hlr_true]]].
  pose proof (@nth_error_some_in lit left jl ll Hll_nth) as Hll_in.
  pose proof (@nth_error_some_in lit right jr lr Hlr_nth) as Hlr_in.
  destruct (lit_eq_dec ll (pivot_pos pivot)) as [Hll_pivot | Hll_not_pivot].
  - subst ll.
    destruct (lit_eq_dec lr (pivot_neg pivot)) as [Hlr_pivot | Hlr_not_neg].
    + subst lr.
      exfalso. eapply lit_eval_pivot_contradiction; eauto.
    + assert (Hlr_not_pos : lr <> pivot_pos pivot).
      { intro Hbad. apply Hright_clean. subst lr. exact Hlr_in. }
      assert (Hin_res : In lr resolvent).
      { apply (proj2 (Hmembers lr)).
        split.
        - right. exact Hlr_in.
        - split; assumption. }
      destruct (@in_nth_error_exists lit lr resolvent Hin_res) as [j Hj].
      exists j, lr. split; assumption.
  - assert (Hll_not_neg : ll <> pivot_neg pivot).
    { intro Hbad. apply Hleft_clean. subst ll. exact Hll_in. }
    assert (Hin_res : In ll resolvent).
    { apply (proj2 (Hmembers ll)).
      split.
      - left. exact Hll_in.
      - split; assumption. }
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
    pose proof (@nth_error_some_in clause known (left_parent step) left Hleft_id) as Hleft_in.
    pose proof (@nth_error_some_in clause known (right_parent step) right Hright_id) as Hright_in.
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
