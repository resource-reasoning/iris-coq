From iris.program_logic Require Export global_functor.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

Definition newlock : val := λ: <>, ref #false.
Definition acquire : val :=
  rec: "lock" "l" := if: CAS '"l" #false #true then #() else '"lock" '"l".
Definition release : val := λ: "l", '"l" <- #false.

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class lockG Σ := SpawnG { lock_tokG :> inG heap_lang Σ (exclR unitC) }.
Definition lockGF : gFunctorList := [GFunctor (constRF (exclR unitC))].
Instance inGF_lockG `{H : inGFs heap_lang Σ lockGF} : lockG Σ.
Proof. destruct H. split. apply: inGF_inG. Qed.

Section proof.
Context {Σ : gFunctors} `{!heapG Σ, !lockG Σ}.
Context (heapN : namespace).
Local Notation iProp := (iPropG heap_lang Σ).

Definition lock_inv (γ : gname) (l : loc) (R : iProp) : iProp :=
  (∃ b : bool, l ↦ #b ★ if b then True else own γ (Excl ()) ★ R)%I.

Definition is_lock (l : loc) (R : iProp) : iProp :=
  (∃ N γ, heapN ⊥ N ∧ heap_ctx heapN ∧ inv N (lock_inv γ l R))%I.

Definition locked (l : loc) (R : iProp) : iProp :=
  (∃ N γ, heapN ⊥ N ∧ heap_ctx heapN ∧
          inv N (lock_inv γ l R) ∧ own γ (Excl ()))%I.

Global Instance lock_inv_ne n γ l : Proper (dist n ==> dist n) (lock_inv γ l).
Proof. solve_proper. Qed.
Global Instance is_lock_ne n l : Proper (dist n ==> dist n) (is_lock l).
Proof. solve_proper. Qed.
Global Instance locked_ne n l : Proper (dist n ==> dist n) (locked l).
Proof. solve_proper. Qed.

(** The main proofs. *)
Global Instance is_lock_persistent l R : PersistentP (is_lock l R).
Proof. apply _. Qed.

Lemma locked_is_lock l R : locked l R ⊢ is_lock l R.
Proof.
  iIntros "Hl"; iDestruct "Hl" as {N γ} "(?&?&?&_)".
  iExists N, γ; by repeat iSplit.
Qed.

Lemma newlock_spec N (R : iProp) Φ :
  heapN ⊥ N →
  (heap_ctx heapN ★ R ★ (∀ l, is_lock l R -★ Φ #l))
  ⊢ WP newlock #() {{ Φ }}.
Proof.
  iIntros {?} "(#Hh & HR & HΦ)". rewrite /newlock.
  wp_seq. iApply wp_pvs. wp_alloc l as "Hl".
  iPvs (own_alloc (Excl ())) as {γ} "Hγ"; first done.
  iPvs (inv_alloc N _ (lock_inv γ l R)) "-[HΦ]" as "#?"; first done.
  { iNext. iExists false. by iFrame "Hl HR". }
  iPvsIntro. iApply "HΦ". iExists N, γ. by repeat iSplit.
Qed.

Lemma acquire_spec l R (Φ : val → iProp) :
  (is_lock l R ★ (locked l R -★ R -★ Φ #())) ⊢ WP acquire #l {{ Φ }}.
Proof.
  iIntros "[Hl HΦ]". iDestruct "Hl" as {N γ} "(%&#?&#?)".
  iLöb as "IH". wp_rec. wp_focus (CAS _ _ _)%E.
  iInv N as "Hinv". iDestruct "Hinv" as {b} "[Hl HR]"; destruct b.
  - wp_cas_fail. iSplitL "Hl".
    + iNext. iExists true. by iSplit.
    + wp_if. by iApply "IH".
  - wp_cas_suc. iDestruct "HR" as "[Hγ HR]". iSplitL "Hl".
    + iNext. iExists true. by iSplit.
    + wp_if. iPvsIntro. iApply "HΦ" "-[HR] HR". iExists N, γ. by repeat iSplit.
Qed.

Lemma release_spec R l (Φ : val → iProp) :
  (locked l R ★ R ★ Φ #()) ⊢ WP release #l {{ Φ }}.
Proof.
  iIntros "(Hl&HR&HΦ)"; iDestruct "Hl" as {N γ} "(%&#?&#?&Hγ)".
  rewrite /release. wp_let.
  iInv N as "Hinv". iDestruct "Hinv" as {b} "[Hl Hγ']"; destruct b.
  - wp_store. iFrame "HΦ". iNext. iExists false. by iFrame "Hl HR Hγ".
  - wp_store. iDestruct "Hγ'" as "[Hγ' _]".
    iCombine "Hγ" "Hγ'" as "Hγ". by iDestruct own_valid "Hγ" as "%".
Qed.
End proof.