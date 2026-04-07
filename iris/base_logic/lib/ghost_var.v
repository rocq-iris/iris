(** A simple "ghost variable" of arbitrary type with fractional ownership.
Can be mutated when fully owned. *)
From iris.algebra Require Import dfrac_agree proofmode_classes frac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

(** The CMRA we need. *)
Class ghost_varG Σ (A : Type) := GhostVarG {
  #[local] ghost_var_inG :: inG Σ (dfrac_agreeR $ leibnizO A);
}.
Global Hint Mode ghost_varG - ! : typeclass_instances.

Definition ghost_varΣ (A : Type) : gFunctors :=
  #[ GFunctor (dfrac_agreeR $ leibnizO A) ].

Global Instance subG_ghost_varΣ Σ A : subG (ghost_varΣ A) Σ → ghost_varG Σ A.
Proof. solve_inG. Qed.

Local Definition ghost_var_def `{!ghost_varG Σ A}
    (γ : gname) (dq : dfrac) (a : A) : iProp Σ :=
  own γ (to_dfrac_agree (A:=leibnizO A) dq a).
Local Definition ghost_var_aux : seal (@ghost_var_def). Proof. by eexists. Qed.
Definition ghost_var := ghost_var_aux.(unseal).
Local Definition ghost_var_unseal :
  @ghost_var = @ghost_var_def := ghost_var_aux.(seal_eq).
Global Arguments ghost_var {Σ A _} γ dq a.

Local Ltac unseal := rewrite ?ghost_var_unseal /ghost_var_def.

Notation "γ ↪VAR dq n" := (ghost_var γ dq n)
  (at level 20, dq custom dfrac at level 1,
   format "γ  ↪VAR dq  n").

(* Compatibility alias. Do not use for new code.
This will eventually be deprecated and removed. *)
Notation ghost_var_frac γ q n := (ghost_var γ (DfracOwn q) n) (only parsing).

Section lemmas.
  Context `{!ghost_varG Σ A}.
  Implicit Types (a b : A) (q : Qp).

  Global Instance ghost_var_timeless γ dq a : Timeless (γ ↪VAR{dq} a).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_var_persistent γ a : Persistent (γ ↪VAR□ a).
  Proof. unseal. apply _. Qed.

  Global Instance ghost_var_fractional γ a : Fractional (λ q, γ ↪VAR{#q} a).
  Proof. intros q1 q2. unseal. rewrite -own_op -frac_agree_op //. Qed.
  Global Instance ghost_var_as_fractional γ a q :
    AsFractional (γ ↪VAR{#q} a) (λ q, γ ↪VAR{#q} a) q.
  Proof. split; [done|]. apply _. Qed.

  Lemma ghost_var_alloc_strong a (P : gname → Prop) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ γ ↪VAR a.
  Proof. unseal. intros. iApply own_alloc_strong; done. Qed.
  Lemma ghost_var_alloc a :
    ⊢ |==> ∃ γ, γ ↪VAR a.
  Proof. unseal. iApply own_alloc. done. Qed.

  Lemma ghost_var_valid_2 γ a1 dq1 a2 dq2 :
    γ ↪VAR{dq1} a1 -∗ γ ↪VAR{dq2} a2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ a1 = a2⌝.
  Proof.
    unseal. iIntros "Hvar1 Hvar2".
    iCombine "Hvar1 Hvar2" gives %[Hq Ha]%dfrac_agree_op_valid.
    done.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma ghost_var_agree γ a1 dq1 a2 dq2 :
    γ ↪VAR{dq1} a1 -∗ γ ↪VAR{dq2} a2 -∗ ⌜a1 = a2⌝.
  Proof.
    iIntros "Hvar1 Hvar2".
    iDestruct (ghost_var_valid_2 with "Hvar1 Hvar2") as %[_ ?]. done.
  Qed.

  Global Instance ghost_var_combine_gives γ a1 dq1 a2 dq2 :
    CombineSepGives (γ ↪VAR{dq1} a1) (γ ↪VAR{dq2} a2) ⌜✓ (dq1 ⋅ dq2) ∧ a1 = a2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[H1 H2].
    eauto.
  Qed.

  Global Instance ghost_var_combine_as γ a1 dq1 a2 dq2 dq :
    IsOp dq dq1 dq2 →
    CombineSepAs (γ ↪VAR{dq1} a1) (γ ↪VAR{dq2} a2) (γ ↪VAR{dq} a1) | 60.
  (* higher cost than the Fractional instance, which is used for a1 = a2 *)
  Proof.
    rewrite /CombineSepAs /IsOp => ->. iIntros "[H1 H2]".
    (* This can't be a single [iCombine] since the instance providing that is
    exactly what we are proving here. *)
    iCombine "H1 H2" gives %[_ ->].
    unseal. iCombine "H1 H2" as "H". rewrite dfrac_agree_op. done.
  Qed.

  (** This is just an instance of fractionality above, but that can be hard to find. *)
  Lemma ghost_var_split γ a q1 q2 :
    γ ↪VAR{#q1 + q2} a -∗ γ ↪VAR{#q1} a ∗ γ ↪VAR{#q2} a.
  Proof. iIntros "[$$]". Qed.

  (** Update the ghost variable to new value [b]. *)
  Lemma ghost_var_update b γ a :
    γ ↪VAR a ==∗ γ ↪VAR b.
  Proof.
    unseal. iApply own_update. apply cmra_update_exclusive. done.
  Qed.
  Lemma ghost_var_update_2 b γ a1 q1 a2 q2 :
    (q1 + q2 = 1)%Qp →
    γ ↪VAR{#q1} a1 -∗ γ ↪VAR{#q2} a2 ==∗ γ ↪VAR{#q1} b ∗ γ ↪VAR{#q2} b.
  Proof.
    intros Hq. unseal. rewrite -own_op. iApply own_update_2.
    apply frac_agree_update_2. done.
  Qed.
  Lemma ghost_var_update_halves b γ a1 a2 :
    γ ↪VAR{#1/2} a1 -∗
    γ ↪VAR{#1/2} a2 ==∗
    γ ↪VAR{#1/2} b ∗ γ ↪VAR{#1/2} b.
  Proof. iApply ghost_var_update_2. apply Qp.half_half. Qed.

  Lemma ghost_var_persist γ dq a :
    γ ↪VAR{dq} a ==∗ γ ↪VAR□ a.
  Proof.
    unseal. iApply own_update. apply dfrac_agree_persist.
  Qed.
  Lemma ghost_var_unpersist γ a :
    γ ↪VAR□ a ==∗ ∃ q, γ ↪VAR{#q} a.
  Proof.
    unseal. iIntros "H".
    iMod (own_updateP with "H") as "H";
      first by apply dfrac_agree_unpersist.
    iDestruct "H" as (? (q&->)) "H".
    iIntros "!>". iExists q. done.
  Qed.

  (** Framing support *)
  Global Instance frame_ghost_var p γ a q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (γ ↪VAR{#q1} a) (γ ↪VAR{#q2} a) (γ ↪VAR{#q} a) | 5.
  Proof. apply: frame_fractional. Qed.

End lemmas.
