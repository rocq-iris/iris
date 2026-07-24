From iris.algebra Require Export cmra.
From iris.bi Require Export sbi plainly.
From iris.bi Require Import derived_laws_later.

Definition internal_cmra_valid {SI : sidx} `{!Sbi PROP} {A : cmra} (a : A) : PROP :=
  <si_pure> siProp_cmra_valid a.
Global Arguments internal_cmra_valid : simpl never.
Global Typeclasses Opaque internal_cmra_valid.
Global Instance: Params (@internal_cmra_valid) 4 := {}.
Notation "✓ a" := (internal_cmra_valid a) : bi_scope.

(** Derived [≼] connective on [cmra] elements. This can be defined on any [bi]
that has internal equality [≡]. It corresponds to the step-indexed [≼{n}]
connective in the [siProp] model. *)
Definition internal_included {SI : sidx} `{!Sbi PROP} {A : cmra} (a b : A) : PROP :=
  ∃ c, b ≡ a ⋅ c.
Global Arguments internal_included : simpl never.
Global Instance: Params (@internal_included) 4 := {}.
Global Typeclasses Opaque internal_included.
Infix "≼" := internal_included : bi_scope.

Section cmra_valid.
  Context {SI : sidx} `{!Sbi PROP}.
  Implicit Types P Q : PROP.

  (* Force implicit argument PROP *)
  Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
  Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).

  Global Instance internal_cmra_valid_ne {A : cmra} :
    NonExpansive (internal_cmra_valid (PROP:=PROP) (A:=A)).
  Proof.
    intros n x x' ?. by apply si_pure_ne, siProp_primitive.cmra_valid_ne.
  Qed.
  Global Instance internal_cmra_valid_proper {A : cmra} :
    Proper ((≡) ==> (⊣⊢)) (internal_cmra_valid (PROP:=PROP) (A:=A)).
  Proof. apply ne_proper, _. Qed.

  Lemma internal_cmra_valid_intro {A : cmra} P (a : A) : ✓ a → P ⊢ (✓ a).
  Proof.
    intros. rewrite (bi.True_intro P) -si_pure_pure.
    by apply si_pure_mono, siProp_primitive.cmra_valid_intro.
  Qed.
  Lemma internal_cmra_valid_elim {A : cmra} (a : A) : ✓ a ⊢ ⌜ ✓{0ᵢ} a ⌝.
  Proof.
    rewrite -si_pure_pure.
    by apply si_pure_mono, siProp_primitive.cmra_valid_elim.
  Qed.
  (* FIXME: Remove in favor of cmra_validN_op_r *)
  Lemma internal_cmra_valid_weaken {A : cmra} (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
  Proof. by apply si_pure_mono, siProp_primitive.cmra_valid_weaken. Qed.
  (** TODO: Remove [SIdxFinite] once we use [SI] instead of [nat] for [siProp]. *)
  Lemma internal_cmra_valid_entails `{!SIdxFinite SI} {A B : cmra} (a : A) (b : B) :
    (✓ a ⊢ ✓ b) ↔ ∀ n, ✓{n} a → ✓{n} b.
  Proof. rewrite si_pure_entails. apply siProp_primitive.valid_entails. Qed.

  Lemma si_pure_internal_cmra_valid {A : cmra} (a : A) : <si_pure> ✓ a ⊣⊢ ✓ a.
  Proof. done. Qed.
  Lemma persistently_internal_cmra_valid {A : cmra} (a : A) : <pers> ✓ a ⊣⊢ ✓ a.
  Proof. apply persistently_si_pure. Qed.
  Lemma plainly_internal_cmra_valid {A : cmra} (a : A) : ■ ✓ a ⊣⊢ ✓ a.
  Proof. apply plainly_si_pure. Qed.
  Lemma intuitionistically_internal_cmra_valid `{!BiAffine PROP} {A : cmra} (a : A) :
    □ ✓ a ⊣⊢ ✓ a.
  Proof.
    by rewrite bi.intuitionistically_into_persistently
      persistently_internal_cmra_valid.
  Qed.
  Lemma internal_cmra_valid_discrete `{!CmraDiscrete A} (a : A) : ✓ a ⊣⊢ ⌜✓ a⌝.
  Proof.
    apply (anti_symm _).
    - rewrite internal_cmra_valid_elim. by apply bi.pure_mono, cmra_discrete_valid.
    - apply bi.pure_elim'=> ?. by apply internal_cmra_valid_intro.
  Qed.

  Global Instance internal_cmra_valid_timeless `{!CmraDiscrete A} (a : A) :
    Timeless (PROP:=PROP) (✓ a).
  Proof. rewrite /Timeless !internal_cmra_valid_discrete. apply (timeless _). Qed.

  Global Instance internal_cmra_valid_absorbing {A : cmra} (a : A) :
    Absorbing (PROP:=PROP) (✓ a).
  Proof. rewrite -persistently_internal_cmra_valid. apply _. Qed.

  Global Instance internal_cmra_valid_plain {A : cmra} (a : A) :
    Plain (PROP:=PROP) (✓ a).
  Proof. rewrite -plainly_internal_cmra_valid. apply _. Qed.

  Global Instance internal_cmra_valid_persistent {A : cmra} (a : A) :
    Persistent (PROP:=PROP) (✓ a).
  Proof. rewrite -persistently_internal_cmra_valid. apply _. Qed.

  Global Instance internal_included_nonexpansive A :
    NonExpansive2 (internal_included (PROP:=PROP) (A:=A)).
  Proof. solve_proper. Qed.
  Global Instance internal_included_proper A :
    Proper ((≡) ==> (≡) ==> (⊣⊢)) (internal_included (PROP:=PROP) (A:=A)).
  Proof. solve_proper. Qed.

  Lemma internal_included_intro {A : cmra} P (a b : A) : a ≼ b → P ⊢ a ≼ b.
  Proof.
    intros [c ->]. rewrite /internal_included -(bi.exist_intro c).
    apply internal_eq_refl.
  Qed.

  Lemma si_pure_internal_included {A : cmra} (a b : A) :
    <si_pure> (a ≼ b) ⊣⊢ a ≼ b.
  Proof. rewrite /internal_included si_pure_exist //. Qed.
  Lemma persistently_internal_included {A : cmra} (a b : A) :
    <pers> (a ≼ b) ⊣⊢ a ≼ b.
  Proof. by rewrite -si_pure_internal_included persistently_si_pure. Qed.
  Lemma plainly_internal_included {A : cmra} (a b : A) : ■ (a ≼ b) ⊣⊢ a ≼ b.
  Proof. by rewrite -si_pure_internal_included plainly_si_pure. Qed.
  Lemma intuitionistically_internal_included `{!BiAffine PROP} {A : cmra} (a b : A) :
    □ (a ≼ b) ⊣⊢ a ≼ b.
  Proof.
    by rewrite bi.intuitionistically_into_persistently
      persistently_internal_included.
  Qed.
  Lemma internal_included_discrete {A : cmra} (a b : A) `{!Discrete b} :
    a ≼ b ⊣⊢ ⌜a ≼ b⌝.
  Proof.
    apply (anti_symm _).
    - apply bi.exist_elim=> a'. rewrite /internal_included bi.pure_exist.
      rewrite -(bi.exist_intro a'). by rewrite discrete_eq.
    - apply bi.pure_elim'=> ?. by apply internal_included_intro.
  Qed.

  Lemma internal_included_refl `{!CmraTotal A} (a : A) : ⊢@{PROP} a ≼ a.
  Proof.
    rewrite /internal_included -(bi.exist_intro (core a)).
    rewrite cmra_core_r. apply internal_eq_refl.
  Qed.
  Lemma internal_included_trans {A : cmra} (a b c : A) :
    ⊢@{PROP} a ≼ b -∗ b ≼ c -∗ a ≼ c.
  Proof.
    apply bi.entails_wand, bi.exist_elim=> a'.
    apply bi.wand_intro_l. rewrite /internal_included bi.sep_exist_r.
    apply bi.exist_elim=> b'. rewrite bi.sep_and -(bi.exist_intro (a' ⋅ b')).
    rewrite -(internal_eq_trans c (b ⋅ b') (a ⋅ _)). f_equiv.
    rewrite assoc. apply: (f_equivI (λ z, z ⋅ b')). solve_proper.
  Qed.

  Global Instance internal_included_timeless {A : cmra} (a b : A) `{!Discrete b} :
    Timeless (PROP:=PROP) (a ≼ b).
  Proof. rewrite /internal_included. apply _. Qed.

  Global Instance internal_included_plain {A : cmra} (a b : A) :
    Plain (PROP:=PROP) (a ≼ b).
  Proof. rewrite /internal_included. apply _. Qed.

  Global Instance internal_included_persistent {A : cmra} (a b : A) :
    Persistent (PROP:=PROP) (a ≼ b).
  Proof. rewrite /internal_included. apply _. Qed.

  Global Instance internal_included_absorbing {A : cmra} (a b : A) :
    Absorbing (PROP:=PROP) (a ≼ b).
  Proof. rewrite /internal_included. apply _. Qed.
End cmra_valid.
