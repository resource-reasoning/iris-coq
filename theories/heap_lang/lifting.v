From iris.base_logic Require Export gen_heap.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import tactics.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
Set Default Proof Using "Type".

Section Lifting.

(** We don’t need any specific formalisation of the heap for this particular language. **)
Variable Sigma : gFunctors.

Hypothesis WPA : action -> iProp Sigma -> iProp Sigma -> Prop.
Hypothesis WPC : condition -> iProp Sigma -> iProp Sigma -> Prop.

(* TODO: Define WPP and WPJ
Definition condition_to_predicate condition state :=
  test_condition state condition = true.
Coercion condition_to_predicate : condition >-> Funclass.

(** We assume that we can translate conditions to formulae on the state.
  Such a translation would probably be done by defining a [heapG] instance,
  using the [atomic_heap] class. **)
Variable condition_to_iProp : condition -> iProp Sigma.

Inductive wpp : command -> iProp Sigma -> iProp Sigma -> Prop :=
  | wpp_jump : forall i C Phi,
    wpp (JumpIf i C) (~ condition_to_iProp C ∗ ▷ Phi)%I Phi
  | wpp_assert : forall i C Phi,
    wpp (Assert C) (condition_to_iProp C ∗ ▷ Phi)%I Phi
  | wpp_action : forall a Phi Psi,
    action_wpp a Phi Psi ->
    wpp (Action a) Phi Psi
  .
*)

Implicit Types Φ : unit → iProp Sigma.

Lemma wp_halted Φ :
  Φ () ⊢ WP Halted {{ Φ }}.
Proof.
  iIntros (<- Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ
}.

Instance heapG_irisG `{heapG Σ} : irisG heap_lang Σ := {
  iris_invG := heapG_invG;
  state_interp := gen_heap_ctx
}.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (atomic _ _) => solve_atomic.
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl.

Local Hint Constructors head_step.
Local Hint Resolve alloc_fresh.
Local Hint Resolve to_of_val.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  unfold IntoVal in *;
  repeat match goal with H : AsVal _ |- _ => destruct H as [??] end; subst;
  apply det_head_step_pure_exec; [ solve_exec_safe | solve_exec_puredet ].

Class AsRec (e : expr) (f x : binder) (erec : expr) :=
  as_rec : e = Rec f x erec.
Instance AsRec_rec f x e : AsRec (Rec f x e) f x e := eq_refl.
Instance AsRec_rec_locked_val v f x e :
  AsRec (of_val v) f x e → AsRec (of_val (locked v)) f x e.
Proof. by unlock. Qed.

Instance pure_rec f x (erec e1 e2 : expr)
    `{!AsVal e2, AsRec e1 f x erec, Closed (f :b: x :b: []) erec} :
  PureExec True (App e1 e2) (subst' x e2 (subst' f e1 erec)).
Proof. unfold AsRec in *; solve_pure_exec. Qed.

Instance pure_unop op e v v' `{!IntoVal e v} :
  PureExec (un_op_eval op v = Some v') (UnOp op e) (of_val v').
Proof. solve_pure_exec. Qed.

Instance pure_binop op e1 e2 v1 v2 v' `{!IntoVal e1 v1, !IntoVal e2 v2} :
  PureExec (bin_op_eval op v1 v2 = Some v') (BinOp op e1 e2) (of_val v').
Proof. solve_pure_exec. Qed.

Instance pure_if_true e1 e2 : PureExec True (If (Lit (LitBool true)) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Instance pure_if_false e1 e2 : PureExec True (If (Lit (LitBool false)) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Instance pure_fst e1 e2 v1 `{!IntoVal e1 v1, !AsVal e2} :
  PureExec True (Fst (Pair e1 e2)) e1.
Proof. solve_pure_exec. Qed.

Instance pure_snd e1 e2 v2 `{!AsVal e1, !IntoVal e2 v2} :
  PureExec True (Snd (Pair e1 e2)) e2.
Proof. solve_pure_exec. Qed.

Instance pure_case_inl e0 v e1 e2 `{!IntoVal e0 v} :
  PureExec True (Case (InjL e0) e1 e2) (App e1 e0).
Proof. solve_pure_exec. Qed.

Instance pure_case_inr e0 v e1 e2 `{!IntoVal e0 v} :
  PureExec True (Case (InjR e0) e1 e2) (App e2 e0).
Proof. solve_pure_exec. Qed.

Section lifting.
Context `{heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork s E e Φ :
  ▷ (Φ (LitV LitUnit) ∗ WP e @ s; ⊤ {{ _, True }}) ⊢ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "[HΦ He]".
  iApply wp_lift_pure_det_head_step; [auto|intros; inv_head_step; eauto|].
  iModIntro; iNext; iIntros "!> /= {$He}". by iApply wp_value.
Qed.
Lemma twp_fork s E e Φ :
  Φ (LitV LitUnit) ∗ WP e @ s; ⊤ [{ _, True }] ⊢ WP Fork e @ s; E [{ Φ }].
Proof.
  iIntros "[HΦ He]".
  iApply twp_lift_pure_det_head_step; [auto|intros; inv_head_step; eauto|].
  iIntros "!> /= {$He}". by iApply twp_value.
Qed.

(** Heap *)
Lemma wp_alloc s E e v :
  IntoVal e v →
  {{{ True }}} Alloc e @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
Proof.
  iIntros (<- Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_alloc with "Hσ") as "[Hσ Hl]"; first done.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
Lemma twp_alloc s E e v :
  IntoVal e v →
  [[{ True }]] Alloc e @ s; E [[{ l, RET LitV (LitLoc l); l ↦ v }]].
Proof.
  iIntros (<- Φ) "_ HΦ". iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>"; iSplit; first by auto.
  iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_alloc with "Hσ") as "[Hσ Hl]"; first done.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_load s E l q v :
  {{{ ▷ l ↦{q} v }}} Load (Lit (LitLoc l)) @ s; E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
Lemma twp_load s E l q v :
  [[{ l ↦{q} v }]] Load (Lit (LitLoc l)) @ s; E [[{ RET v; l ↦{q} v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto.
  iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_store s E l v' e v :
  IntoVal e v →
  {{{ ▷ l ↦ v' }}} Store (Lit (LitLoc l)) e @ s; E {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (<- Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.
Lemma twp_store s E l v' e v :
  IntoVal e v →
  [[{ l ↦ v' }]] Store (Lit (LitLoc l)) e @ s; E [[{ RET LitV LitUnit; l ↦ v }]].
Proof.
  iIntros (<- Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.

Lemma wp_cas_fail s E l q v' e1 v1 e2 :
  IntoVal e1 v1 → AsVal e2 → v' ≠ v1 → vals_cas_compare_safe v' v1 →
  {{{ ▷ l ↦{q} v' }}} CAS (Lit (LitLoc l)) e1 e2 @ s; E
  {{{ RET LitV (LitBool false); l ↦{q} v' }}}.
Proof.
  iIntros (<- [v2 <-] ?? Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
Lemma twp_cas_fail s E l q v' e1 v1 e2 :
  IntoVal e1 v1 → AsVal e2 → v' ≠ v1 → vals_cas_compare_safe v' v1 →
  [[{ l ↦{q} v' }]] CAS (Lit (LitLoc l)) e1 e2 @ s; E
  [[{ RET LitV (LitBool false); l ↦{q} v' }]].
Proof.
  iIntros (<- [v2 <-] ?? Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (v2' σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas_suc s E l e1 v1 e2 v2 :
  IntoVal e1 v1 → IntoVal e2 v2 → vals_cas_compare_safe v1 v1 →
  {{{ ▷ l ↦ v1 }}} CAS (Lit (LitLoc l)) e1 e2 @ s; E
  {{{ RET LitV (LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (<- <- ? Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.
Lemma twp_cas_suc s E l e1 v1 e2 v2 :
  IntoVal e1 v1 → IntoVal e2 v2 → vals_cas_compare_safe v1 v1 →
  [[{ l ↦ v1 }]] CAS (Lit (LitLoc l)) e1 e2 @ s; E
  [[{ RET LitV (LitBool true); l ↦ v2 }]].
Proof.
  iIntros (<- <- ? Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.

Lemma wp_faa s E l i1 e2 i2 :
  IntoVal e2 (LitV (LitInt i2)) →
  {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Lit (LitLoc l)) e2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (<- Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.
Lemma twp_faa s E l i1 e2 i2 :
  IntoVal e2 (LitV (LitInt i2)) →
  [[{ l ↦ LitV (LitInt i1) }]] FAA (Lit (LitLoc l)) e2 @ s; E
  [[{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }]].
Proof.
  iIntros (<- Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.
End lifting.
