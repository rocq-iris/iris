(** This file exposes a generic interface for an arbitrary implementation of
later credits via the [BiLaterCredits], [BiBUpdLaterCredits] and [BiFUpdLaterCredits]
typeclasses. They state the primitive laws for later credits and their interaction
with [bupd] and [fupd], which let you split and allocate later credits, and use
them to eliminate laters, respectively. See [base_logic/lib/later_credits.v] and
[bi/monpred.v] for instantiations of these typeclasses. *)
From iris.bi Require Import interface derived_laws_later updates.
Import interface.bi derived_laws.bi derived_laws_later.bi.

(* We enable primitive projections in this file to improve the performance of the Iris proofmode:
    primitive projections for the bi-records makes the proofmode faster.
*)
Local Set Primitive Projections.

(* The sections add extra BI assumptions, which is only picked up with "Type"*. *)
Set Default Proof Using "Type*".

Class LaterCredits (PROP : Type) : Type := lc : nat → PROP.
Global Hint Mode LaterCredits ! : typeclass_instances.
Global Typeclasses Opaque lc.

Notation "'£'  n" := (lc n).

Class BiLaterCreditsMixin {SI : sidx} (PROP : bi) `(LaterCredits PROP) := {
  bi_lc_mixin_lc_split n m : £ (n + m) ⊣⊢@{PROP} £ n ∗ £ m;
  bi_lc_mixin_lc_timeless n : Timeless (PROP:=PROP) (£ n);
  bi_lc_mixin_lc_0_persistent : Persistent (PROP:=PROP) (£ 0);
  bi_lc_mixin_lc_affine n : Affine (PROP:=PROP) (£ n);
}.

Class BiLaterCredits {SI : sidx} (PROP : bi) := {
  #[global] bi_lc_lc :: LaterCredits PROP;
  bi_lc_mixin : BiLaterCreditsMixin PROP bi_lc_lc;
}.
Global Hint Mode BiLaterCredits - ! : typeclass_instances.
Global Arguments bi_lc_lc : simpl never.

Class BiBUpdLaterCredits {SI : sidx} (PROP : bi)
    `{!BiLaterCredits PROP, !BiBUpd PROP} :=
  lc_zero : ⊢@{PROP} |==> £ 0.
Global Hint Mode BiBUpdLaterCredits - ! - - : typeclass_instances.

(** [lc_fupd_elim_later] allows to eliminate a later from a hypothesis at an update.
This is typically used as [iMod (lc_fupd_elim_later with "Hcredit HP") as "HP".],
where ["Hcredit"] is a credit available in the context and ["HP"] is the
assumption from which a later should be stripped. *)
Class BiFUpdLaterCredits {SI : sidx} (PROP : bi)
    `{!BiLaterCredits PROP, !BiFUpd PROP} :=
  lc_fupd_elim_later E (P : PROP) : £ 1 -∗ (▷ P) -∗ |={E}=> P.
Global Hint Mode BiFUpdLaterCredits - ! - - : typeclass_instances.

Section lc_laws.
  Context {SI : sidx} `{!BiLaterCredits PROP}.

  Lemma lc_split n m : £ (n + m) ⊣⊢@{PROP} £ n ∗ £ m.
  Proof. apply bi_lc_mixin. Qed.

  Global Instance lc_timeless n : Timeless (PROP:=PROP) (£ n).
  Proof. apply bi_lc_mixin. Qed.

  Global Instance lc_0_persistent : Persistent (PROP:=PROP) (£ 0).
  Proof. apply bi_lc_mixin. Qed.

  Global Instance lc_0_affine n : Affine (PROP:=PROP) (£ n).
  Proof. apply bi_lc_mixin. Qed.
End lc_laws.

Section lc_derived.
  Context {SI : sidx} `{!BiLaterCredits PROP}.

  Lemma lc_succ n : £ (S n) ⊣⊢@{PROP} £ 1 ∗ £ n.
  Proof. rewrite -lc_split //=. Qed.

  Lemma lc_weaken {n} m : m ≤ n → £ n ⊢@{PROP} £ m.
  Proof. intros [k ->]%Nat.le_sum. rewrite lc_split sep_elim_l //. Qed.
End lc_derived.

Section lc_fupd_derived.
  Context {SI : sidx} `{!BiLaterCredits PROP, !BiFUpd PROP, !BiFUpdLaterCredits PROP}.
  Implicit Types P : PROP.

  (** If the goal is a fancy update, this lemma can be used to make a later appear
      in front of it in exchange for a later credit. This is typically used as
      [iApply (lc_fupd_add_later with "Hcredit")], where ["Hcredit"] is a credit
      available in the context. *)
  Lemma lc_fupd_add_later E1 E2 P :
    £ 1 -∗ (▷ |={E1,E2}=> P) -∗ |={E1,E2}=> P.
  Proof.
    apply entails_wand, wand_intro_r. etrans; last apply (fupd_trans E1 E1).
    apply wand_elim_l', wand_entails. apply lc_fupd_elim_later.
  Qed.

  (** Similar to above, but here we are adding [n] laters. *)
  Lemma lc_fupd_add_laterN E1 E2 P n :
    £ n -∗ (▷^n |={E1,E2}=> P) -∗ |={E1,E2}=> P.
  Proof.
    apply entails_wand, wand_intro_r. induction n as [|n IH]; simpl.
    { rewrite sep_elim_r //. }
    rewrite lc_succ -assoc (later_intro (£ n)) later_sep_2 IH.
    apply wand_elim_l', wand_entails, lc_fupd_add_later.
  Qed.

  Lemma lc_fupd_add_step_fupdN E1 E2 E3 P n :
    £ n -∗ (|={E1}[E2]▷=>^n |={E1,E3}=> P) -∗ |={E1,E3}=> P.
  Proof.
    apply entails_wand, wand_intro_r. induction n as [|n IH]; simpl.
    { rewrite sep_elim_r //. }
    rewrite lc_succ -assoc step_fupd_frame_l IH fupd_frame_l.
    apply fupd_elim. rewrite fupd_trans.
    apply wand_elim_l', wand_entails, lc_fupd_add_later.
  Qed.
End lc_fupd_derived.
