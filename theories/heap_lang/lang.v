From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.algebra Require Export ofe.
From stdpp Require Export strings.
From stdpp Require Import gmap.
Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Parameter state : Type.
Parameter action : Type.
Parameter condition : Type.

Parameter apply_action : state -> action -> state.
Parameter test_condition : state -> condition -> bool.

Parameter action_eq : EqDecision action.
Declare Instance : EqDecision action.
Parameter action_Countable : Countable action.
Declare Instance : Countable action.

Parameter condition_eq : EqDecision condition.
Declare Instance : EqDecision condition.
Parameter condition_Countable : Countable condition.
Declare Instance : Countable condition.

Parameter CTrue : condition.
Parameter CTrue_spec : forall st, test_condition st CTrue = true.

Module heap_lang.
Open Scope Z_scope.

Definition position := positive.

Inductive command :=
  | Action (a : action)
  | JumpIf (target : position) (C : condition)
  | Assert (C : condition)
  .

Definition program := list command.

Definition read (p : program) (pc : position) : option command :=
  nth_error p (Pos.to_nat pc).

Bind Scope command_scope with command.

Inductive value :=
  | value_position (pc : position)
  | value_halted
  .

Bind Scope val_scope with val.

Instance position_eq : EqDecision position.
Proof. refine _. Defined.

Instance position_countable : Countable position.
Proof. refine _. Qed.

Instance command_eq : EqDecision command.
Proof. solve_decision. Defined.

Instance command_countable : Countable command.
Proof.
(*
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 end)
  (λ n, match n with 0 => NegOp | _ => MinusUnOp end) _); by intros [].
*)
Admitted.

Instance value_eq : EqDecision value.
Proof. solve_decision. Defined.

Instance value_countable : Countable value.
Proof.
  refine (inj_countable' (fun v => match v with value_halted => Pos.of_nat 0 | value_position pc => Pos.add 1 pc end)
    (fun n => if decide (n = (Pos.of_nat 0)) then value_halted else value_position (Pos.sub n 1)) _).
  intros [pc|].
  - rewrite decide_False.
    + apply f_equal. admit.
    + admit.
  - apply decide_True; by reflexivity.
Admitted.

Instance command_inhabited : Inhabited command := populate (Assert CTrue).
Instance value_inhabited : Inhabited value := populate value_halted.

Canonical Structure stateC := leibnizC state.
Canonical Structure valC := leibnizC value.
Canonical Structure commandC := leibnizC command.

Definition command_eval (st : state) (pc : position) (c : command) : option (state * position) :=
  match c with
  | Action a => Some (apply_action st a, Pos.add 1 pc)
  | JumpIf target C =>
    if test_condition st C then Some (st, target)
    else None
  | Assert C =>
    if test_condition st C then Some (st, Pos.add 1 pc)
    else None
  end.

Definition position_eval (st : state) (p : program) (pc : position) : option (state * value) :=
  match read p pc with
  | None => Some (st, value_halted)
  | Some c =>
    match command_eval st pc c with
    | None => None
    | Some (st, p) => Some (st, value_position p)
    end
  end.

Definition full_state : Type := state * program.

Inductive head_step : position → full_state → position → full_state → list (position) → Prop :=
  | head_step_cons pc st p st' pc' :
    position_eval st p pc = Some (st', value_position pc') ->
    head_step pc (st, p) pc' (st', p) []
  .

Lemma val_head_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 e2 σ2 efs :
  head_step (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; by eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
    end; auto.
Qed.

Lemma alloc_fresh e v σ :
  let l := fresh (dom (gset loc) σ) in
  to_val e = Some v → head_step (Alloc e) σ (Lit (LitLoc l)) (<[l:=v]>σ) [].
Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

(* Misc *)
Lemma to_val_rec f x e `{!Closed (f :b: x :b: []) e} :
  to_val (Rec f x e) = Some (RecV f x e).
Proof. rewrite /to_val. case_decide=> //. do 2 f_equal; apply proof_irrel. Qed.

(** Closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_of_val X v : is_closed X (of_val v).
Proof. apply is_closed_weaken_nil. induction v; simpl; auto. Qed.

Lemma is_closed_to_val X e v : to_val e = Some v → is_closed X e.
Proof. intros <-%of_to_val. apply is_closed_of_val. Qed.

Lemma is_closed_subst X e x es :
  is_closed [] es → is_closed (x :: X) e → is_closed X (subst x es e).
Proof.
  intros ?. revert X.
  induction e=> X /= ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_do_subst' X e x es :
  is_closed [] es → is_closed (x :b: X) e → is_closed X (subst' x es e).
Proof. destruct x; eauto using is_closed_subst. Qed.

(* Substitution *)
Lemma subst_is_closed X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  revert X. induction e=> X /=; rewrite ?bool_decide_spec ?andb_True=> ??;
    repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_nil e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply subst_is_closed with []; set_solver. Qed.

Lemma subst_subst e x es es' :
  Closed [] es' → subst x es (subst x es' e) = subst x es' e.
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst' e x es es' :
  Closed [] es' → subst' x es (subst' x es' e) = subst' x es' e.
Proof. destruct x; simpl; auto using subst_subst. Qed.

Lemma subst_subst_ne e x y es es' :
  Closed [] es → Closed [] es' → x ≠ y →
  subst x es (subst y es' e) = subst y es' (subst x es e).
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using eq_sym, subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst_ne' e x y es es' :
  Closed [] es → Closed [] es' → x ≠ y →
  subst' x es (subst' y es' e) = subst' y es' (subst' x es e).
Proof. destruct x, y; simpl; auto using subst_subst_ne with congruence. Qed.

Lemma subst_rec' f y e x es :
  x = f ∨ x = y ∨ x = BAnon →
  subst' x es (Rec f y e) = Rec f y e.
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.
Lemma subst_rec_ne' f y e x es :
  (x ≠ f ∨ f = BAnon) → (x ≠ y ∨ y = BAnon) →
  subst' x es (Rec f y e) = Rec f y (subst' x es e).
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.

Lemma heap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.
End heap_lang.

(** Language *)
Canonical Structure heap_ectxi_lang := EctxiLanguage heap_lang.heap_lang_mixin.
Canonical Structure heap_ectx_lang := EctxLanguageOfEctxi heap_ectxi_lang.
Canonical Structure heap_lang := LanguageOfEctx heap_ectx_lang.

(* Prefer heap_lang names over ectx_language names. *)
Export heap_lang.

(** Define some derived forms. *)
Notation Lam x e := (Rec BAnon x e) (only parsing).
Notation Let x e1 e2 := (App (Lam x e2) e1) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV x e := (RecV BAnon x e) (only parsing).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)) (only parsing).

Notation Skip := (Seq (Lit LitUnit) (Lit LitUnit)).
