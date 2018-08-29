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

Instance command_inhabited : Inhabited command := populate (Assert CTrue).

Canonical Structure stateC := leibnizC state.
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

Definition position_eval (st : state) (p : program) (pc : position) : option (state * option position) :=
  match read p pc with
  | None => Some (st, None)
  | Some c =>
    match command_eval st pc c with
    | None => None
    | Some (st, p) => Some (st, Some p)
    end
  end.

(** In this language, what is called the state in Iris includes the program. **)
Definition full_state : Type := state * program.

Inductive head_step : option position → full_state → option position → full_state → list (option position) → Prop :=
  | head_step_cons pc st p st' pc' :
    position_eval st p pc = Some (st', pc') ->
    head_step (Some pc) (st, p) pc' (st', p) []
  .

(** There is only one value: the [None] construct, where the program is halted **)
Definition value := unit.

Definition of_value (_ : unit) : option position := None.
Definition to_value (pc : option position) :=
  match pc with
  | None => Some tt
  | Some _ => None
  end.

(** Similarly, evaluation contexts are useless in such a language. **)
Definition context : Type := False.

Definition fill_context (K : context) : option position -> option position :=
  match K with end.

Lemma heap_lang_mixin : EctxiLanguageMixin of_value to_value fill_context head_step.
Proof.
  split; repeat intro; repeat match goal with v : unit |- _ => destruct v end; auto;
    try solve [ repeat match goal with pc : option _ |- _ => destruct pc
                | H : _ |- _ => solve [ inversion H ] end; auto ].
Qed.

End heap_lang.

(** Language *)
Canonical Structure heap_ectxi_lang := EctxiLanguage heap_lang.heap_lang_mixin.
Canonical Structure heap_ectx_lang := EctxLanguageOfEctxi heap_ectxi_lang.
Canonical Structure heap_lang := LanguageOfEctx heap_ectx_lang.

(* Prefer heap_lang names over ectx_language names. *)
Export heap_lang.
