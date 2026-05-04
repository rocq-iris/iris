(** This file is still experimental. See its tracking issue
https://gitlab.mpi-sws.org/iris/iris/-/issues/439 for details on remaining
issues before stabilization. *)
(** Ghost state for a append-only list, wrapping the [mono_listR] RA. This
  provides three assertions:
  - an authoritative proposition [γ ↪●ML{dq} l] for the authoritative
    list [l]
  - a persistent assertion [γ ↪◯ML l] witnessing that the authoritative
    list is at least [l]
  - a persistent assertion [γ ↪◯ML[i] a] witnessing that the index [i]
    is [a] in the authoritative list.

The key rules are [mono_list_auth_lb_own_valid], which asserts that an auth at [l]
and a lower-bound at [l'] imply that [l' `prefix_of` l], and [mono_list_update],
which allows one to grow the auth element by appending only. At any time the
auth list can be "snapshotted" with [mono_list_lb_own_get] to produce a
persistent lower-bound. *)
From iris.proofmode Require Import proofmode.
From iris.algebra.lib Require Import mono_list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

Class mono_listG (A : Type) Σ :=
  MonoListG { #[local] mono_list_inG :: inG Σ (mono_listR (leibnizO A)) }.

Definition mono_listΣ (A : Type) : gFunctors :=
  #[GFunctor (mono_listR (leibnizO A))].

Global Instance subG_mono_listΣ {A Σ} :
  subG (mono_listΣ A) Σ → (mono_listG A) Σ.
Proof. solve_inG. Qed.

Local Definition mono_list_auth_own_def `{!mono_listG A Σ}
    (γ : gname) (dq : dfrac) (l : list A) : iProp Σ :=
  own γ (●ML{dq} (l : listO (leibnizO A))).
Local Definition mono_list_auth_own_aux : seal (@mono_list_auth_own_def).
Proof. by eexists. Qed.
Definition mono_list_auth_own := mono_list_auth_own_aux.(unseal).
Local Definition mono_list_auth_own_unseal :
  @mono_list_auth_own = @mono_list_auth_own_def := mono_list_auth_own_aux.(seal_eq).
Global Arguments mono_list_auth_own {A Σ _} γ dq l.

Local Definition mono_list_lb_own_def `{!mono_listG A Σ}
    (γ : gname) (l : list A) : iProp Σ :=
  own γ (◯ML (l : listO (leibnizO A))).
Local Definition mono_list_lb_own_aux : seal (@mono_list_lb_own_def).
Proof. by eexists. Qed.
Definition mono_list_lb_own := mono_list_lb_own_aux.(unseal).
Local Definition mono_list_lb_own_unseal :
  @mono_list_lb_own = @mono_list_lb_own_def := mono_list_lb_own_aux.(seal_eq).
Global Arguments mono_list_lb_own {A Σ _} γ l.

Definition mono_list_idx_own `{!mono_listG A Σ}
    (γ : gname) (i : nat) (a : A) : iProp Σ :=
  ∃ l : list A, ⌜ l !! i = Some a ⌝ ∗ mono_list_lb_own γ l.

Notation "γ ↪●ML dq l" := (mono_list_auth_own γ dq l)
  (at level 20, dq custom dfrac at level 1,
   format "γ  ↪●ML dq  l").
Notation "γ ↪◯ML l" := (mono_list_lb_own γ l)
  (at level 20, l at level 20).
Notation "γ ↪◯ML[ i ] a " := (mono_list_idx_own γ i a)
  (at level 20, format "γ  ↪◯ML[ i ]  a") : bi_scope.

Local Ltac unseal := rewrite
  /mono_list_idx_own ?mono_list_auth_own_unseal /mono_list_auth_own_def
  ?mono_list_lb_own_unseal /mono_list_lb_own_def.

Section mono_list_own.
  Context `{!mono_listG A Σ}.
  Implicit Types (l : list A) (i : nat) (a : A).

  Global Instance mono_list_auth_own_timeless γ dq l : Timeless (γ ↪●ML{dq} l).
  Proof. unseal. apply _. Qed.
  Global Instance mono_list_auth_own_persistent γ l : Persistent (γ ↪●ML□ l).
  Proof. unseal. apply _. Qed.
  Global Instance mono_list_lb_own_timeless γ l : Timeless (γ ↪◯ML l).
  Proof. unseal. apply _. Qed.
  Global Instance mono_list_lb_own_persistent γ l : Persistent (γ ↪◯ML l).
  Proof. unseal. apply _. Qed.
  Global Instance mono_list_idx_own_timeless γ i a :
    Timeless (γ ↪◯ML[i] a) := _.
  Global Instance mono_list_idx_own_persistent γ i a :
    Persistent (γ ↪◯ML[i] a) := _.

  Global Instance mono_list_auth_own_fractional γ l :
    Fractional (λ q, γ ↪●ML{#q} l).
  Proof. unseal. intros p q. by rewrite -own_op -mono_list_auth_dfrac_op. Qed.
  Global Instance mono_list_auth_own_as_fractional γ q l :
    AsFractional (γ ↪●ML{#q} l) (λ q, γ ↪●ML{#q} l) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma mono_list_auth_own_agree γ dq1 dq2 l1 l2 :
    γ ↪●ML{dq1} l1 -∗ γ ↪●ML{dq2} l2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ l1 = l2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    by iCombine "H1 H2" gives %?%mono_list_auth_dfrac_op_valid_L.
  Qed.
  Lemma mono_list_auth_own_exclusive γ l1 l2 :
    γ ↪●ML l1 -∗ γ ↪●ML l2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (mono_list_auth_own_agree with "H1 H2") as %[]; done.
  Qed.

  Lemma mono_list_auth_lb_own_valid γ dq l1 l2 :
    γ ↪●ML{dq} l1 -∗ γ ↪◯ML l2 -∗ ⌜✓ dq ∧ l2 `prefix_of` l1 ⌝.
  Proof.
    unseal. iIntros "Hauth Hlb".
    by iCombine "Hauth Hlb" gives %?%mono_list_both_dfrac_valid_L.
  Qed.

  Lemma mono_list_lb_own_valid γ l1 l2 :
    γ ↪◯ML l1 -∗
    γ ↪◯ML l2 -∗
    ⌜ l1 `prefix_of` l2 ∨ l2 `prefix_of` l1 ⌝.
  Proof.
    unseal. iIntros "H1 H2".
    by iCombine "H1 H2" gives %?%mono_list_lb_op_valid_L.
  Qed.

  Lemma mono_list_idx_agree γ i a1 a2 :
    γ ↪◯ML[i] a1 -∗ γ ↪◯ML[i] a2 -∗ ⌜ a1 = a2 ⌝.
  Proof.
    iDestruct 1 as (l1 Hl1) "H1". iDestruct 1 as (l2 Hl2) "H2".
    iDestruct (mono_list_lb_own_valid with "H1 H2") as %Hpre.
    iPureIntro.
    destruct Hpre as [Hpre|Hpre]; eapply prefix_lookup_Some in Hpre; eauto; congruence.
  Qed.

  Lemma mono_list_auth_idx_lookup γ dq l i a :
    γ ↪●ML{dq} l -∗ γ ↪◯ML[i] a -∗ ⌜ l !! i = Some a ⌝.
  Proof.
    iIntros "Hauth". iDestruct 1 as (l1 Hl1) "Hl1".
    iDestruct (mono_list_auth_lb_own_valid with "Hauth Hl1") as %[_ Hpre].
    iPureIntro.
    eapply prefix_lookup_Some in Hpre; eauto; congruence.
  Qed.

  Lemma mono_list_lb_own_get γ dq l :
    γ ↪●ML{dq} l ⊢ γ ↪◯ML l.
  Proof. intros. unseal. by apply own_mono, mono_list_included. Qed.
  Lemma mono_list_lb_own_le {γ l} l' :
    l' `prefix_of` l →
    γ ↪◯ML l ⊢ γ ↪◯ML l'.
  Proof. unseal. intros. by apply own_mono, mono_list_lb_mono. Qed.

  Lemma mono_list_lb_own_nil γ :
    ⊢ |==> γ ↪◯ML [].
  Proof. unseal. iApply own_unit. Qed.

  Lemma mono_list_idx_own_get {γ l} i a :
    l !! i = Some a →
    γ ↪◯ML l -∗ γ ↪◯ML[i] a.
  Proof. iIntros (Hli) "Hl". iExists l. by iFrame. Qed.

  Lemma mono_list_own_alloc l :
    ⊢ |==> ∃ γ, γ ↪●ML l ∗ γ ↪◯ML l.
  Proof.
    unseal. setoid_rewrite <- own_op. by apply own_alloc, mono_list_both_valid_L.
  Qed.
  Lemma mono_list_auth_own_update {γ l} l' :
    l `prefix_of` l' →
    γ ↪●ML l ==∗ γ ↪●ML l' ∗ γ ↪◯ML l'.
  Proof.
    iIntros (?) "Hauth".
    iAssert (γ ↪●ML l') with "[> Hauth]" as "Hauth".
    { unseal. iApply (own_update with "Hauth"). by apply mono_list_update. }
    iModIntro. iSplit; [done|]. by iApply mono_list_lb_own_get.
  Qed.

  Lemma mono_list_auth_own_update_app {γ l} l' :
    γ ↪●ML l ==∗
    γ ↪●ML (l ++ l') ∗ γ ↪◯ML (l ++ l').
  Proof. by apply mono_list_auth_own_update, prefix_app_r. Qed.

  Lemma mono_list_auth_own_persist γ dq l :
    γ ↪●ML{dq} l ==∗ γ ↪●ML□ l.
  Proof.
    unseal. iApply own_update. apply mono_list_auth_persist.
  Qed.
  Lemma mono_list_auth_own_unpersist γ l :
    γ ↪●ML□ l ==∗ ∃ q, γ ↪●ML{#q} l.
  Proof.
    unseal. iIntros "H".
    iMod (own_updateP with "H") as "H";
      first by apply mono_list_auth_unpersist.
    iDestruct "H" as (? (q&->)) "H".
    iIntros "!>". iExists q. done.
  Qed.
End mono_list_own.
