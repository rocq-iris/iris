(** Ghost state for a monotonically increasing nat, wrapping the [mono_natR]
RA. Provides an authoritative proposition [mono_nat_auth_own γ q n] for the
underlying number [n] and a persistent proposition [mono_nat_lb_own γ m]
witnessing that the authoritative nat is at least [m].

The key rules are [mono_nat_auth_lb_own_valid], which asserts that an auth at [n] and
a lower-bound at [m] imply that [m ≤ n], and [mono_nat_update], which allows to
increase the auth element. At any time the auth nat can be "snapshotted" with
[mono_nat_get_lb] to produce a persistent lower-bound proposition. *)
From iris.proofmode Require Import proofmode.
From iris.algebra.lib Require Import mono_nat.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

Class mono_natG Σ :=
  MonoNatG { #[local] mono_natG_inG :: inG Σ mono_natR; }.

Definition mono_natΣ : gFunctors := #[ GFunctor mono_natR ].
Global Instance subG_mono_natΣ Σ : subG mono_natΣ Σ → mono_natG Σ.
Proof. solve_inG. Qed.

Local Definition mono_nat_auth_own_def `{!mono_natG Σ}
    (γ : gname) (dq : dfrac) (n : nat) : iProp Σ :=
  own γ (●MN{dq} n).
Local Definition mono_nat_auth_own_aux : seal (@mono_nat_auth_own_def).
Proof. by eexists. Qed.
Definition mono_nat_auth_own := mono_nat_auth_own_aux.(unseal).
Local Definition mono_nat_auth_own_unseal :
  @mono_nat_auth_own = @mono_nat_auth_own_def := mono_nat_auth_own_aux.(seal_eq).
Global Arguments mono_nat_auth_own {Σ _} γ dq n.

Local Definition mono_nat_lb_own_def `{!mono_natG Σ} (γ : gname) (n : nat): iProp Σ :=
  own γ (◯MN n).
Local Definition mono_nat_lb_own_aux : seal (@mono_nat_lb_own_def). Proof. by eexists. Qed.
Definition mono_nat_lb_own := mono_nat_lb_own_aux.(unseal).
Local Definition mono_nat_lb_own_unseal :
  @mono_nat_lb_own = @mono_nat_lb_own_def := mono_nat_lb_own_aux.(seal_eq).
Global Arguments mono_nat_lb_own {Σ _} γ n.

Notation "γ ↪●MN dq n" := (mono_nat_auth_own γ dq n)
  (at level 20, dq custom dfrac at level 1,
   format "γ  ↪●MN dq  n").
Notation "γ ↪◯MN n" := (mono_nat_lb_own γ n)
  (at level 20).

(* Compatibility alias. Do not use for new code.
This will eventually be deprecated and removed. *)
Notation mono_nat_auth_own_frac γ q n :=
  (mono_nat_auth_own γ (DfracOwn q) n) (only parsing).

Local Ltac unseal := rewrite
  ?mono_nat_auth_own_unseal /mono_nat_auth_own_def
  ?mono_nat_lb_own_unseal /mono_nat_lb_own_def.

Section mono_nat.
  Context `{!mono_natG Σ}.
  Implicit Types (n m : nat).

  Global Instance mono_nat_auth_own_timeless γ dq n : Timeless (γ ↪●MN{dq} n).
  Proof. unseal. apply _. Qed.
  Global Instance mono_nat_auth_own_persistent γ n : Persistent (γ ↪●MN□ n).
  Proof. unseal. apply _. Qed.
  Global Instance mono_nat_lb_own_timeless γ n : Timeless (γ ↪◯MN n).
  Proof. unseal. apply _. Qed.
  Global Instance mono_nat_lb_own_persistent γ n : Persistent (γ ↪◯MN n).
  Proof. unseal. apply _. Qed.

  Global Instance mono_nat_auth_own_fractional γ n :
    Fractional (λ q, γ ↪●MN{#q} n).
  Proof. unseal. intros p q. rewrite -own_op -mono_nat_auth_dfrac_op //. Qed.
  Global Instance mono_nat_auth_own_as_fractional γ q n :
    AsFractional (γ ↪●MN{#q} n) (λ q, γ ↪●MN{#q} n) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma mono_nat_auth_own_agree γ dq1 dq2 n1 n2 :
    γ ↪●MN{dq1} n1 -∗
    γ ↪●MN{dq2} n2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ n1 = n2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iCombine "H1 H2" gives %?%mono_nat_auth_dfrac_op_valid; done.
  Qed.
  Lemma mono_nat_auth_own_exclusive γ n1 n2 :
    γ ↪●MN n1 -∗ γ ↪●MN n2 -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (mono_nat_auth_own_agree with "H1 H2") as %[[] _].
  Qed.

  Lemma mono_nat_auth_lb_own_valid γ dq n m :
    γ ↪●MN{dq} n -∗ γ ↪◯MN m -∗ ⌜✓ dq ∧ m ≤ n⌝.
  Proof.
    unseal. iIntros "Hauth Hlb".
    iCombine "Hauth Hlb" gives %Hvalid%mono_nat_both_dfrac_valid.
    auto.
  Qed.

  (** The conclusion of this lemma is persistent; the proofmode will preserve
  the [mono_nat_auth_own] in the premise as long as the conclusion is introduced
  to the persistent context, for example with [iDestruct (mono_nat_lb_own_get
  with "Hauth") as "#Hfrag"]. *)
  Lemma mono_nat_lb_own_get γ dq n :
    γ ↪●MN{dq} n -∗ γ ↪◯MN n.
  Proof. unseal. iApply own_mono. apply mono_nat_included. Qed.

  Lemma mono_nat_lb_own_le {γ n} n' :
    n' ≤ n →
    γ ↪◯MN n -∗ γ ↪◯MN n'.
  Proof. unseal. intros. iApply own_mono. by apply mono_nat_lb_mono. Qed.

  Lemma mono_nat_lb_own_0 γ :
    ⊢ |==> γ ↪◯MN 0.
  Proof. unseal. iApply own_unit. Qed.

  Lemma mono_nat_own_alloc_strong P n :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ γ ↪●MN n ∗ γ ↪◯MN n.
  Proof.
    unseal. intros.
    iMod (own_alloc_strong (●MN n ⋅ ◯MN n) P) as (γ) "[% [??]]"; first done.
    { apply mono_nat_both_valid; auto. }
    auto with iFrame.
  Qed.
  Lemma mono_nat_own_alloc n :
    ⊢ |==> ∃ γ, γ ↪●MN n ∗ γ ↪◯MN n.
  Proof.
    iMod (mono_nat_own_alloc_strong (λ _, True) n) as (γ) "[_ ?]".
    - by apply pred_infinite_True.
    - eauto.
  Qed.

  Lemma mono_nat_own_update {γ n} n' :
    n ≤ n' →
    γ ↪●MN n ==∗ γ ↪●MN n' ∗ γ ↪◯MN n'.
  Proof.
    iIntros (?) "Hauth".
    iAssert (γ ↪●MN n') with "[> Hauth]" as "Hauth".
    { unseal. iApply (own_update with "Hauth"). by apply mono_nat_update. }
    iModIntro. iSplit; [done|]. by iApply mono_nat_lb_own_get.
  Qed.

  Lemma mono_nat_own_persist γ dq a :
    γ ↪●MN{dq} a ==∗ γ ↪●MN□ a.
  Proof.
    unseal. iApply own_update. apply mono_nat_auth_persist.
  Qed.
  Lemma mono_nat_own_unpersist γ a :
    γ ↪●MN□ a ==∗ ∃ q, γ ↪●MN{#q} a.
  Proof.
    unseal. iIntros "H".
    iMod (own_updateP with "H") as "H";
      first by apply mono_nat_auth_unpersist.
    iDestruct "H" as (? (q&->)) "H".
    iIntros "!>". iExists q. done.
  Qed.
End mono_nat.
