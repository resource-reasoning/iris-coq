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

Parameter apply_action : state -> action -> state -> Prop.

Parameter action_eq : EqDecision action.
Declare Instance : EqDecision action.
Parameter action_Countable : Countable action.
Declare Instance : Countable action.

Parameter condition_eq : EqDecision condition.
Declare Instance : EqDecision condition.
Parameter condition_Countable : Countable condition.
Declare Instance : Countable condition.

Parameter CTrue : condition.
Parameter CFalse : condition.

Parameter DCTrueCFalse : CTrue <> CFalse.

Parameter condition_reduce : condition -> state -> condition -> Prop.

Module heap_lang.
Open Scope Z_scope.

Definition position := positive.

(** Definition of commands **)
Inductive command :=
  | Action (a : action)
  | JumpIf (target : position) (C : condition)
  | Assert (C : condition)
  .

(** Expressions carry what is need to continue the execution.
  At first, I thought that expression would only consist of
  positions.
  However, some commands need to be reduced in several steps.
  For instance, an [Assert C] command must first reduce to a
  [Assert CTrue] command to be executed. **)

Inductive expression :=
  | PC (pc : position)
  | PCC (pc : position) (c : command)
  | Halted
  .

Definition program := list command.

Definition read (p : program) (pc : position) : option command :=
  nth_error p (Pos.to_nat pc).

Bind Scope command_scope with command.

(** Only the [Halted] expression doesn’t reduce.
   The value type is thus a type with only one inhabitant: unit. **)

Definition of_val (_ : ()) := Halted.
Definition to_val e :=
  match e with
  | Halted => Some ()
  | _ => None
  end.

(** Small-step states includes the state, but also the program. **)
Definition ssstate : Type := state * program.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof. destruct v. intro E. by destruct e. Qed.

(** Typeclasses **)

Instance position_eq : EqDecision position.
Proof. refine _. Defined.

Instance position_countable : Countable position.
Proof. refine _. Qed.

Instance command_eq : EqDecision command.
Proof. solve_decision. Defined.

Definition encode_command c :=
  match c with
  | Action a => inl (inl a)
  | JumpIf target C => inl (inr (target, C))
  | Assert C => inr C
  end.

Definition decode_command c :=
  match c with
  | inl (inl a) => Action a
  | inl (inr (target, C)) => JumpIf target C
  | inr C => Assert C
  end.

Instance command_countable : Countable command.
Proof. refine (inj_countable' encode_command decode_command _); by intros []. Qed.

Instance expression_eq : EqDecision expression.
Proof. solve_decision. Defined.

Definition encode_expression e :=
  match e with
  | PC pc => inl (inl pc)
  | PCC pc c => inl (inr (pc, c))
  | Halted => inr ()
  end.

Definition decode_expression e :=
  match e with
  | inl (inl pc) => PC pc
  | inl (inr (pc, c)) => PCC pc c
  | inr () => Halted
  end.

Instance expression_countable : Countable expression.
Proof. refine (inj_countable' encode_expression decode_expression _); by intros []. Qed.

Instance command_inhabited : Inhabited command := populate (Assert CFalse).
Instance expression_inhabited : Inhabited expression := populate Halted.

Canonical Structure ssstateC := leibnizC ssstate.
Canonical Structure commandC := leibnizC command.
Canonical Structure unitC := leibnizC unit.
Canonical Structure expressionC := leibnizC expression.

(** Evaluation contexts **)

(** The only cases whee we could use evaluation contexts in this language
   is when a condition  has to be reduced to either [CTrue] or [CFalse].
   This can happen in either the [JumpIf] case or the [Assert] case.
   However, the type constraints on the function [fill_context] in Iris
   assume that (1) the function [fill_context] is from expressions to
   expressions, and (2), that it is complete.  The first issue is
   problematical as in the only place where contexts appear in our
   language, contexts take conditions and not expressions.  In other
   words, our language is sorted: conditions are not commands.  We could
   solve this issue by stating that expressions consider all possible
   sorts of our language, but then the issue (2) comes into place: what
   is the result of filling a context with an object of a different
   type than its hole?  This is of course meaningless.  Iris’s contexts
   are thus not suitable for our language.  This is frustrating, given
   the simplicity of our example. **)

Definition context : Type := False.

Definition fill_context (K : context) : expression -> expression :=
  match K with end.

Inductive head_step : expression -> ssstate -> expression -> ssstate -> list expression -> Prop :=
  | head_step_halt p st pc :
    read p pc = None ->
    head_step (PC pc) (st, p) Halted (st, p) []
  | head_step_read p st pc c :
    read p pc = Some c ->
    head_step (PC pc) (st, p) (PCC pc c) (st, p) []
  | head_step_action p st st' pc a :
    apply_action st a st' ->
    head_step (PCC pc (Action a)) (st, p) (PC (1 + pc)%positive) (st', p) []
  | head_step_jump_reduce p st pc target C C' :
    condition_reduce C st C' ->
    head_step (PCC pc (JumpIf target C)) (st, p) (PCC pc (JumpIf target C')) (st, p) []
  | head_step_assert_reduce p st pc C C' :
    condition_reduce C st C' ->
    head_step (PCC pc (Assert C)) (st, p) (PCC pc (Assert C')) (st, p) []
  | head_step_jump_true p st pc target :
    head_step (PCC pc (JumpIf target CTrue)) (st, p) (PC target) (st, p) []
  | head_step_jump_false p st pc target :
    head_step (PCC pc (JumpIf target CFalse)) (st, p) (PC (1 + pc)%positive) (st, p) []
  | head_step_assert_true p st pc :
    head_step (PCC pc (Assert CTrue)) (st, p) (PC (1 + pc)%positive) (st, p) []
  .

Lemma heap_lang_mixin : EctxiLanguageMixin of_val to_val fill_context head_step.
Proof.
  split; repeat intro; repeat match goal with v : unit |- _ => destruct v end; auto;
    try solve [ repeat match goal with
                | e : expression |- _ => destruct e
                | H : _ |- _ => solve [ inversion H ] end; auto ].
Qed.

Lemma val_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

End heap_lang.

(** Language *)
Canonical Structure heap_ectxi_lang := EctxiLanguage heap_lang.heap_lang_mixin.
Canonical Structure heap_ectx_lang := EctxLanguageOfEctxi heap_ectxi_lang.
Canonical Structure heap_lang := LanguageOfEctx heap_ectx_lang.

(* Prefer heap_lang names over ectx_language names. *)
Export heap_lang.
