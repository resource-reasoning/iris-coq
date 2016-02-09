Require Export program_logic.model.

Definition ownI {Λ Σ} (i : positive) (P : iProp Λ Σ) : iProp Λ Σ :=
  uPred_own (Res {[ i ↦ to_agree (Later (iProp_unfold P)) ]} ∅ ∅).
Arguments ownI {_ _} _ _%I.
Definition ownP {Λ Σ} (σ: state Λ) : iProp Λ Σ := uPred_own (Res ∅ (Excl σ) ∅).
Definition ownG {Λ Σ} (m: iGst Λ Σ) : iProp Λ Σ := uPred_own (Res ∅ ∅ (Some m)).
Instance: Params (@ownI) 3.
Instance: Params (@ownP) 2.
Instance: Params (@ownG) 2.

Typeclasses Opaque ownI ownG ownP.

Section ownership.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types r : iRes Λ Σ.
Implicit Types σ : state Λ.
Implicit Types P : iProp Λ Σ.
Implicit Types m : iGst Λ Σ.

(* Invariants *)
Global Instance ownI_contractive i : Contractive (@ownI Λ Σ i).
Proof.
  intros n P Q HPQ.
  apply (_: Proper (_ ==> _) iProp_unfold), Later_contractive in HPQ.
  by unfold ownI; rewrite HPQ.
Qed.
Lemma always_ownI i P : (□ ownI i P)%I ≡ ownI i P.
Proof.
  apply uPred.always_own.
  by rewrite Res_unit !cmra_unit_empty map_unit_singleton.
Qed.
Global Instance ownI_always_stable i P : AlwaysStable (ownI i P).
Proof. by rewrite /AlwaysStable always_ownI. Qed.
Lemma ownI_sep_dup i P : ownI i P ≡ (ownI i P ★ ownI i P)%I.
Proof. apply (uPred.always_sep_dup' _). Qed.

(* physical state *)
Lemma ownP_twice σ1 σ2 : (ownP σ1 ★ ownP σ2 : iProp Λ Σ) ⊑ False.
Proof.
  rewrite /ownP -uPred.own_op Res_op.
  by apply uPred.own_invalid; intros (_&?&_).
Qed.
Global Instance ownP_timeless σ : TimelessP (@ownP Λ Σ σ).
Proof. rewrite /ownP; apply _. Qed.

(* ghost state *)
Global Instance ownG_ne n : Proper (dist n ==> dist n) (@ownG Λ Σ).
Proof. by intros m m' Hm; unfold ownG; rewrite Hm. Qed.
Global Instance ownG_proper : Proper ((≡) ==> (≡)) (@ownG Λ Σ) := ne_proper _.
Lemma ownG_op m1 m2 : ownG (m1 ⋅ m2) ≡ (ownG m1 ★ ownG m2)%I.
Proof. by rewrite /ownG -uPred.own_op Res_op !(left_id _ _). Qed.
Lemma always_ownG_unit m : (□ ownG (unit m))%I ≡ ownG (unit m).
Proof.
  apply uPred.always_own.
  by rewrite Res_unit !cmra_unit_empty -{2}(cmra_unit_idempotent m).
Qed.
Lemma ownG_valid m : (ownG m) ⊑ (✓ m).
Proof. by rewrite /ownG uPred.own_valid; apply uPred.valid_mono=> n [? []]. Qed.
Lemma ownG_valid_r m : (ownG m) ⊑ (ownG m ★ ✓ m).
Proof. apply (uPred.always_entails_r' _ _), ownG_valid. Qed.
Global Instance ownG_timeless m : Timeless m → TimelessP (ownG m).
Proof. rewrite /ownG; apply _. Qed.

(* inversion lemmas *)
Lemma ownI_spec r n i P :
  ✓{n} r →
  (ownI i P) n r ↔ wld r !! i ={n}= Some (to_agree (Later (iProp_unfold P))).
Proof.
  intros [??]; rewrite /uPred_holds/=res_includedN/=singleton_includedN; split.
  * intros [(P'&Hi&HP) _]; rewrite Hi.
    by apply Some_dist, symmetry, agree_valid_includedN,
      (cmra_included_includedN _ P'),HP; apply map_lookup_validN with (wld r) i.
  * intros ?; split_ands; try apply cmra_empty_leastN; eauto.
Qed.
Lemma ownP_spec r n σ : ✓{n} r → (ownP σ) n r ↔ pst r ={n}= Excl σ.
Proof.
  intros (?&?&?); rewrite /uPred_holds /= res_includedN /= Excl_includedN //.
  naive_solver (apply cmra_empty_leastN).
Qed.
Lemma ownG_spec r n m : (ownG m) n r ↔ Some m ≼{n} gst r.
Proof.
  rewrite /uPred_holds /= res_includedN; naive_solver (apply cmra_empty_leastN).
Qed.
End ownership.