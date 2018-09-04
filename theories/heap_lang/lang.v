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
  [Assert CTrue] command to be executed.
  I also added an [Error] case.  This is not a return value:
  it is just an expression with no semantics.  It is being
  needed as Iris supposes that the [fill_item] function is
  total, which is obviously not the case in a typed setting.
  I thus need a dummy expression for this case.  A better
  fix would be to change Iris altogether to make it accept
  non-total [fill_item] functions. **)

(** Expect that this would not ork because Iris forces the
  [fill_item] function to take an expression (Iris has
  clearly not be done with types in mind… at least not in
  the analysed programming laguage—this is so frustrating!)
  and not something else, like a condition.  We could add
  again a dummy case for that, but this is going to be too
  strange. **)

Inductive expression :=
  | PC (pc : position)
  | PCC (pc : position) (c : command)
  | Halted
  | Error
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
  | Halted => inr (inl ())
  | Error => inr (inr ())
  end.

Definition decode_expression e :=
  match e with
  | inl (inl pc) => PC pc
  | inl (inr (pc, c)) => PCC pc c
  | inr (inl ()) => Halted
  | inr (inr ()) => Error
  end.

Instance expression_countable : Countable expression.
Proof. refine (inj_countable' encode_expression decode_expression _); by intros []. Qed.

Instance command_inhabited : Inhabited command := populate (Assert CFalse).
Instance expression_inhabited : Inhabited expression := populate Error.

Canonical Structure ssstateC := leibnizC ssstate.
Canonical Structure commandC := leibnizC command.
Canonical Structure unitC := leibnizC unit.
Canonical Structure expressionC := leibnizC expression.

(** Evaluation contexts **)

(** The only cases when we use evaluation contexts in this language is when a condition
   has to be reduced to either [CTrue] or [CFalse].  This can happen in either the
   [JumpIf] case or the [Assert] case. **)

Inductive context :=
  | context_JumpIf (pc : position) (target : position)

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
