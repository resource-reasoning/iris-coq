From iris.algebra Require Export cmra.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

(* This is isomorphic to option, but has a very different RA structure. *)
Inductive dec_agree (A : Type) : Type := 
  | DecAgree : A → dec_agree A
  | DecAgreeBot : dec_agree A.
Arguments DecAgree {_} _.
Arguments DecAgreeBot {_}.
Instance maybe_DecAgree {A} : Maybe (@DecAgree A) := λ x,
  match x with DecAgree a => Some a | _ => None end.

Section dec_agree.
Context {A : Type} `{∀ x y : A, Decision (x = y)}.

Instance dec_agree_valid : Valid (dec_agree A) := λ x,
  if x is DecAgree _ then True else False.
Instance dec_agree_equiv : Equiv (dec_agree A) := equivL.
Canonical Structure dec_agreeC : cofeT := leibnizC (dec_agree A).

Instance dec_agree_op : Op (dec_agree A) := λ x y,
  match x, y with
  | DecAgree a, DecAgree b => if decide (a = b) then DecAgree a else DecAgreeBot
  | _, _ => DecAgreeBot
  end.
Instance dec_agree_pcore : PCore (dec_agree A) := Some.

Definition dec_agree_ra_mixin : RAMixin (dec_agree A).
Proof.
  split.
  - apply _.
  - intros x y cx ? [=<-]; eauto.
  - apply _.
  - intros [?|] [?|] [?|]; by repeat (simplify_eq/= || case_match).
  - intros [?|] [?|]; by repeat (simplify_eq/= || case_match).
  - intros [?|] ? [=<-]; by repeat (simplify_eq/= || case_match).
  - intros [?|]; by repeat (simplify_eq/= || case_match).
  - intros [?|] [?|] ?? [=<-]; eauto.
  - by intros [?|] [?|] ?.
Qed.

Canonical Structure dec_agreeR : cmraT :=
  discreteR (dec_agree A) dec_agree_ra_mixin.

(* Some properties of this CMRA *)
Global Instance dec_agree_persistent (x : dec_agreeR) : Persistent x.
Proof. by constructor. Qed.

Lemma dec_agree_ne a b : a ≠ b → DecAgree a ⋅ DecAgree b = DecAgreeBot.
Proof. intros. by rewrite /= decide_False. Qed.

Lemma dec_agree_idemp (x : dec_agree A) : x ⋅ x = x.
Proof. destruct x; by rewrite /= ?decide_True. Qed.

Lemma dec_agree_op_inv (x1 x2 : dec_agree A) : ✓ (x1 ⋅ x2) → x1 = x2.
Proof. destruct x1, x2; by repeat (simplify_eq/= || case_match). Qed.
End dec_agree.

Arguments dec_agreeC : clear implicits.
Arguments dec_agreeR _ {_}.
