From stdpp Require Import coPset.
From iris.bi Require Import interface derived_laws_later big_op plainly.
Import interface.bi derived_laws.bi derived_laws_later.bi.

(* We enable primitive projections in this file to improve the performance of the Iris proofmode:
    primitive projections for the bi-records makes the proofmode faster.
*)
Local Set Primitive Projections.

(* The sections add extra BI assumptions, which is only picked up with "Type"*. *)
Set Default Proof Using "Type*".

(* We first define operational type classes for the notations, and then later
bundle these operational type classes with the laws. *)
Class BUpd (PROP : Type) : Type := bupd : PROP → PROP.
Global Instance : Params (@bupd) 2 := {}.
Global Hint Mode BUpd ! : typeclass_instances.
Global Arguments bupd {_}%_type_scope {_} _%_bi_scope.
Global Typeclasses Opaque bupd.

Notation "|==> Q" := (bupd Q) : bi_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q)%I : bi_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q) : stdpp_scope.

Class FUpd (PROP : Type) : Type := fupd : coPset → coPset → PROP → PROP.
Global Instance: Params (@fupd) 4 := {}.
Global Hint Mode FUpd ! : typeclass_instances.
Global Arguments fupd {_}%_type_scope {_} _ _ _%_bi_scope.
Global Typeclasses Opaque fupd.

Notation "|={ E1 , E2 }=> Q" := (fupd E1 E2 Q) : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q)%I : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q) : stdpp_scope.

Notation "|={ E }=> Q" := (fupd E E Q) : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q)%I : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q) : stdpp_scope.

(** Bundled versions  *)
(* Mixins allow us to create instances easily without having to use Program *)
Record BiBUpdMixin (PROP : bi) `(BUpd PROP) := {
  bi_bupd_mixin_bupd_ne : NonExpansive (bupd (PROP:=PROP));
  bi_bupd_mixin_bupd_intro (P : PROP) : P ⊢ |==> P;
  bi_bupd_mixin_bupd_mono (P Q : PROP) : (P ⊢ Q) → (|==> P) ⊢ |==> Q;
  bi_bupd_mixin_bupd_trans (P : PROP) : (|==> |==> P) ⊢ |==> P;
  bi_bupd_mixin_bupd_frame_r (P R : PROP) : (|==> P) ∗ R ⊢ |==> P ∗ R;
}.

Record BiFUpdMixin (PROP : bi) `(FUpd PROP) := {
  bi_fupd_mixin_fupd_ne E1 E2 :
    NonExpansive (fupd (PROP:=PROP) E1 E2);
  bi_fupd_mixin_fupd_mask_subseteq E1 E2 :
    E2 ⊆ E1 → ⊢@{PROP} |={E1,E2}=> |={E2,E1}=> emp;
  bi_fupd_mixin_except_0_fupd E1 E2 (P : PROP) :
    ◇ (|={E1,E2}=> P) ⊢ |={E1,E2}=> P;
  bi_fupd_mixin_fupd_mono E1 E2 (P Q : PROP) :
    (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q;
  bi_fupd_mixin_fupd_trans E1 E2 E3 (P : PROP) :
    (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P;
  bi_fupd_mixin_fupd_mask_frame_r' E1 E2 Ef (P : PROP) :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P;
  bi_fupd_mixin_fupd_frame_r E1 E2 (P R : PROP) :
    (|={E1,E2}=> P) ∗ R ⊢ |={E1,E2}=> P ∗ R;
}.

Class BiBUpd (PROP : bi) := {
  #[global] bi_bupd_bupd :: BUpd PROP;
  bi_bupd_mixin : BiBUpdMixin PROP bi_bupd_bupd;
}.
Global Hint Mode BiBUpd ! : typeclass_instances.
Global Arguments bi_bupd_bupd : simpl never.

Class BiFUpd (PROP : bi) := {
  #[global] bi_fupd_fupd :: FUpd PROP;
  bi_fupd_mixin : BiFUpdMixin PROP bi_fupd_fupd;
}.
Global Hint Mode BiFUpd ! : typeclass_instances.
Global Arguments bi_fupd_fupd : simpl never.

Class BiBUpdFUpd (PROP : bi) `{BiBUpd PROP, BiFUpd PROP} :=
  bupd_fupd E (P : PROP) : (|==> P) ⊢ |={E}=> P.
Global Hint Mode BiBUpdFUpd ! - - : typeclass_instances.

Class BiBUpdSbi (PROP : bi) `{!BiBUpd PROP, !Sbi PROP} :=
  bupd_si_pure Pi : (|==> <si_pure> Pi) ⊢@{PROP} <si_pure> Pi.
Global Hint Mode BiBUpdSbi ! - - : typeclass_instances.

(** These rules for the interaction between [<si_pure>] and the [|={E1,E2=>]
modality only make sense for affine logics. For general BIs we do not know the
canonical set of rules and linear models in which they might hold. *)
Class BiFUpdSbi (PROP : bi) `{!BiFUpd PROP, !Sbi PROP} := {
  (** This rule allows you to use the current context for proving a purely
  step-indexed proposition [Pi] *without* actually using up the context. You can
  then continue the proof in the second conjunct. The mask-changing version
  [fupd_si_pure_keep] can be derived. *)
  fupd_keep_si_pure' {E} E' Pi (R : PROP) :
    (|={E,E'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E}=∗ R) ⊢ |={E}=> R;
  (** Later "almost" commutes with fancy updates over plain propositions. It
  commutes "almost" because of the ◇ modality, which is needed in the definition
  of fancy updates so one can remove laters of timeless propositions. *)
  fupd_si_pure_later E Pi :
    (▷ |={E}=> <si_pure> Pi) ⊢@{PROP} |={E}=> ▷ ◇ <si_pure> Pi;
  (** Forall quantifiers commute with fancy updates over plain propositions. *)
  fupd_si_pure_forall_2 E {A} (Φi : A → siProp) :
    (∀ x, |={E}=> <si_pure> Φi x) ⊢@{PROP} |={E}=> ∀ x, <si_pure> Φi x
}.
Global Hint Mode BiBUpdFUpd ! - - : typeclass_instances.

(** * Step-taking fancy updates. *)
(** These have two masks, but they are different than the two masks of a
mask-changing update: in [|={Eo}[Ei]▷=> Q], the first mask [Eo] ("outer mask")
holds at the beginning and the end; the second mask [Ei] ("inner mask") holds
around the [▷]. This is also why we use a different notation than for the two
masks of a mask-changing updates. *)
Notation "|={ Eo } [ Ei ]▷=> Q" := (|={Eo,Ei}=> ▷ |={Ei,Eo}=> Q)%I : bi_scope.
Notation "P ={ Eo } [ Ei ]▷=∗ Q" := (P -∗ |={Eo}[Ei]▷=> Q)%I : bi_scope.
Notation "P ={ Eo } [ Ei ]▷=∗ Q" := (P -∗ |={Eo}[Ei]▷=> Q) : stdpp_scope.

Notation "|={ E }▷=> Q" := (|={E}[E]▷=> Q)%I : bi_scope.
Notation "P ={ E }▷=∗ Q" := (P ={E}[E]▷=∗ Q)%I : bi_scope.
Notation "P ={ E }▷=∗ Q" := (P ={E}[E]▷=∗ Q) : stdpp_scope.

(** For the iterated version, in principle there are 4 masks: "outer" and
"inner" of [|={Eo}[Ei]▷=>], as well as "begin" and "end" masks [E1] and [E2]
that could potentially differ from [Eo]. The latter can be obtained from
this notation by adding normal mask-changing update modalities:
[|={E1,Eo}=> |={Eo}[Ei]▷=>^n |={Eo,E2}=> Q] *)
Fixpoint step_fupdN `{!BiFUpd PROP} (Eo Ei : coPset) (n : nat) (P : PROP) : PROP :=
  match n with
  | 0 => P
  | S n => |={Eo}[Ei]▷=> step_fupdN Eo Ei n P
  end.
Global Instance: Params (@step_fupdN) 5 := {}.
Global Typeclasses Opaque step_fupdN.

Notation "|={ Eo } [ Ei ]▷=>^ n Q" := (step_fupdN Eo Ei n Q) : bi_scope.
Notation "P ={ Eo } [ Ei ]▷=∗^ n Q" := (P -∗ |={Eo}[Ei]▷=>^n Q)%I : bi_scope.
Notation "P ={ Eo } [ Ei ]▷=∗^ n Q" := (P -∗ |={Eo}[Ei]▷=>^n Q) : stdpp_scope.

Notation "|={ E }▷=>^ n Q" := (|={E}[E]▷=>^n Q)%I : bi_scope.
Notation "P ={ E }▷=∗^ n Q" := (P ={E}[E]▷=∗^n Q)%I : bi_scope.
Notation "P ={ E }▷=∗^ n Q" := (P ={E}[E]▷=∗^n Q) : stdpp_scope.

Section bupd_laws.
  Context {PROP : bi} `{!BiBUpd PROP}.
  Implicit Types P : PROP.

  Global Instance bupd_ne : NonExpansive (@bupd PROP _).
  Proof. eapply bi_bupd_mixin_bupd_ne, bi_bupd_mixin. Qed.
  Lemma bupd_intro P : P ⊢ |==> P.
  Proof. eapply bi_bupd_mixin_bupd_intro, bi_bupd_mixin. Qed.
  Lemma bupd_mono (P Q : PROP) : (P ⊢ Q) → (|==> P) ⊢ |==> Q.
  Proof. eapply bi_bupd_mixin_bupd_mono, bi_bupd_mixin. Qed.
  Lemma bupd_trans (P : PROP) : (|==> |==> P) ⊢ |==> P.
  Proof. eapply bi_bupd_mixin_bupd_trans, bi_bupd_mixin. Qed.
  Lemma bupd_frame_r (P R : PROP) : (|==> P) ∗ R ⊢ |==> P ∗ R.
  Proof. eapply bi_bupd_mixin_bupd_frame_r, bi_bupd_mixin. Qed.
End bupd_laws.

Section fupd_laws.
  Context {PROP : bi} `{!BiFUpd PROP}.
  Implicit Types P : PROP.

  Global Instance fupd_ne E1 E2 : NonExpansive (@fupd PROP _ E1 E2).
  Proof. eapply bi_fupd_mixin_fupd_ne, bi_fupd_mixin. Qed.
  (** [iMod] with this lemma is useful to change the current mask to a subset,
  and obtain a fupd for changing it back. For the case where you want to get rid
  of a mask-changing fupd in the goal, [iApply fupd_mask_intro] avoids having to
  specify the mask. *)
  Lemma fupd_mask_subseteq {E1} E2 : E2 ⊆ E1 → ⊢@{PROP} |={E1,E2}=> |={E2,E1}=> emp.
  Proof. eapply bi_fupd_mixin_fupd_mask_subseteq, bi_fupd_mixin. Qed.
  Lemma except_0_fupd E1 E2 (P : PROP) : ◇ (|={E1,E2}=> P) ⊢ |={E1,E2}=> P.
  Proof. eapply bi_fupd_mixin_except_0_fupd, bi_fupd_mixin. Qed.
  Lemma fupd_mono E1 E2 (P Q : PROP) : (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q.
  Proof. eapply bi_fupd_mixin_fupd_mono, bi_fupd_mixin. Qed.
  Lemma fupd_trans E1 E2 E3 (P : PROP) : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P.
  Proof. eapply bi_fupd_mixin_fupd_trans, bi_fupd_mixin. Qed.
  Lemma fupd_mask_frame_r' E1 E2 Ef (P : PROP) :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P.
  Proof. eapply bi_fupd_mixin_fupd_mask_frame_r', bi_fupd_mixin. Qed.
  Lemma fupd_frame_r E1 E2 (P R : PROP) : (|={E1,E2}=> P) ∗ R ⊢ |={E1,E2}=> P ∗ R.
  Proof. eapply bi_fupd_mixin_fupd_frame_r, bi_fupd_mixin. Qed.
End fupd_laws.

Section bupd_derived.
  Context {PROP : bi} `{!BiBUpd PROP}.
  Implicit Types P Q R : PROP.

  Global Instance bupd_proper :
    Proper ((≡) ==> (≡)) (bupd (PROP:=PROP)) := ne_proper _.

  (** BUpd derived rules *)
  Global Instance bupd_mono' : Proper ((⊢) ==> (⊢)) (bupd (PROP:=PROP)).
  Proof. intros P Q; apply bupd_mono. Qed.
  Global Instance bupd_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) (bupd (PROP:=PROP)).
  Proof. intros P Q; apply bupd_mono. Qed.

  Lemma bupd_frame_l R Q : (R ∗ |==> Q) ⊢ |==> R ∗ Q.
  Proof. rewrite !(comm _ R); apply bupd_frame_r. Qed.
  Lemma bupd_wand_l P Q : (P -∗ Q) ∗ (|==> P) ⊢ |==> Q.
  Proof. by rewrite bupd_frame_l wand_elim_l. Qed.
  Lemma bupd_wand_r P Q : (|==> P) ∗ (P -∗ Q) ⊢ |==> Q.
  Proof. by rewrite bupd_frame_r wand_elim_r. Qed.
  Lemma bupd_sep P Q : (|==> P) ∗ (|==> Q) ⊢ |==> P ∗ Q.
  Proof. by rewrite bupd_frame_r bupd_frame_l bupd_trans. Qed.
  Lemma bupd_idemp P : (|==> |==> P) ⊣⊢ |==> P.
  Proof.
    apply: anti_symm.
    - apply bupd_trans.
    - apply bupd_intro.
  Qed.

  Global Instance bupd_sep_homomorphism :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (bupd (PROP:=PROP)).
  Proof. split; [split|]; try apply _; [apply bupd_sep | apply bupd_intro]. Qed.

  Lemma bupd_or P Q : (|==> P) ∨ (|==> Q) ⊢ |==> (P ∨ Q).
  Proof. apply or_elim; apply bupd_mono; [ apply or_intro_l | apply or_intro_r ]. Qed.

  Global Instance bupd_or_homomorphism :
    MonoidHomomorphism bi_or bi_or (flip (⊢)) (bupd (PROP:=PROP)).
  Proof. split; [split|]; try apply _; [apply bupd_or | apply bupd_intro]. Qed.

  Lemma bupd_and P Q : (|==> (P ∧ Q)) ⊢ (|==> P) ∧ (|==> Q).
  Proof. apply and_intro; apply bupd_mono; [apply and_elim_l | apply and_elim_r]. Qed.

  Lemma bupd_exist A (Φ : A → PROP) : (∃ x : A, |==> Φ x) ⊢ |==> ∃ x : A, Φ x.
  Proof. apply exist_elim=> a. by rewrite -(exist_intro a). Qed.

  Lemma bupd_forall A (Φ : A → PROP) : (|==> ∀ x : A, Φ x) ⊢ ∀ x : A, |==> Φ x.
  Proof. apply forall_intro=> a. by rewrite -(forall_elim a). Qed.

  Lemma big_sepL_bupd {A} (Φ : nat → A → PROP) l :
    ([∗ list] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_bupd {A} `{Countable K} (Φ : K → A → PROP) l :
    ([∗ map] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepM2_bupd {A B} `{Countable K} (Φ : K → A → B → PROP) l1 l2 :
    ([∗ map] k↦a;b ∈ l1;l2, |==> Φ k a b) ⊢ |==> [∗ map] k↦a;b ∈ l1;l2, Φ k a b.
  Proof.
    rewrite !big_sepM2_alt big_sepM_bupd.
    rewrite !persistent_and_affinely_sep_l bupd_frame_l //.
  Qed.
  Lemma big_sepS_bupd `{Countable A} (Φ : A → PROP) l :
    ([∗ set]  x ∈ l, |==> Φ x) ⊢ |==> [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_bupd `{Countable A} (Φ : A → PROP) l :
    ([∗ mset] x ∈ l, |==> Φ x) ⊢ |==> [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_bupd P : ◇ (|==> P) ⊢ (|==> ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using bupd_mono, or_intro_r.
    by rewrite -bupd_intro -or_intro_l.
  Qed.

  Global Instance bupd_absorbing P :
    Absorbing P → Absorbing (|==> P).
  Proof. rewrite /Absorbing /bi_absorbingly bupd_frame_l =>-> //. Qed.

  Section bupd_sbi.
    Context `{!Sbi PROP, !BiBUpdSbi PROP}.

    Lemma bupd_plainly P : (|==> ■ P) ⊢ ■ P.
    Proof. apply bupd_si_pure. Qed.

    Lemma bupd_plainly_elim P `{!Absorbing P} : (|==> ■ P) ⊢ P.
    Proof. by rewrite bupd_plainly plainly_elim. Qed.

    Lemma bupd_elim P `{!Plain P, !Absorbing P} : (|==> P) ⊢ P.
    Proof.
      by rewrite {1}(plain P) /plainly bupd_si_pure si_pure_si_emp_valid_elim.
    Qed.

    Lemma bupd_plain_forall {A} (Φ : A → PROP)
        `{!∀ x, Plain (Φ x), !∀ x, Absorbing (Φ x)} :
      (|==> ∀ x, Φ x) ⊣⊢ (∀ x, |==> Φ x).
    Proof.
      apply (anti_symm _).
      - apply bupd_forall.
      - rewrite -bupd_intro. apply forall_intro=> x.
        by rewrite (forall_elim x) bupd_elim.
    Qed.

    Global Instance bupd_plain P : Plain P → Plain (|==> P).
    Proof.
      intros. rewrite /Plain. rewrite {1}(plain P) {1}bupd_elim.
      by rewrite -bupd_intro.
    Qed.
  End bupd_sbi.
End bupd_derived.

Section fupd_derived.
  Context {PROP : bi} `{!BiFUpd PROP}.
  Implicit Types P Q R : PROP.

  Global Instance fupd_proper E1 E2 :
    Proper ((≡) ==> (≡)) (fupd (PROP:=PROP) E1 E2) := ne_proper _.

  (** FUpd derived rules *)
  Global Instance fupd_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (fupd (PROP:=PROP) E1 E2).
  Proof. intros P Q; apply fupd_mono. Qed.
  Global Instance fupd_flip_mono' E1 E2 :
    Proper (flip (⊢) ==> flip (⊢)) (fupd (PROP:=PROP) E1 E2).
  Proof. intros P Q; apply fupd_mono. Qed.

  Lemma fupd_mask_intro_subseteq E1 E2 P :
    E2 ⊆ E1 → P ⊢ |={E1,E2}=> |={E2,E1}=> P.
  Proof.
    intros HE.
    apply wand_entails', wand_intro_r.
    rewrite fupd_mask_subseteq; last exact: HE.
    rewrite !fupd_frame_r. rewrite left_id. done.
  Qed.
  Lemma fupd_intro E P : P ⊢ |={E}=> P.
  Proof. by rewrite {1}(fupd_mask_intro_subseteq E E P) // fupd_trans. Qed.
  Lemma fupd_except_0 E1 E2 P : (|={E1,E2}=> ◇ P) ⊢ |={E1,E2}=> P.
  Proof. by rewrite {1}(fupd_intro E2 P) except_0_fupd fupd_trans. Qed.
  Lemma fupd_idemp E P : (|={E}=> |={E}=> P) ⊣⊢ |={E}=> P.
  Proof.
    apply: anti_symm.
    - apply fupd_trans.
    - apply fupd_intro.
  Qed.

  (** Weaken the first mask of the goal from [E1] to [E2].
      This lemma is intended to be [iApply]ed.
      However, usually you can [iMod (fupd_mask_subseteq E2)] instead and that
      will be slightly more convenient. *)
  Lemma fupd_mask_weaken {E1} E2 {E3 P} :
    E2 ⊆ E1 →
    ((|={E2,E1}=> emp) ={E2,E3}=∗ P) ⊢ |={E1,E3}=> P.
  Proof.
    intros HE.
    apply wand_entails', wand_intro_r.
    rewrite {1}(fupd_mask_subseteq E2) //.
    rewrite fupd_frame_r. by rewrite wand_elim_r fupd_trans.
  Qed.

  (** Introduction lemma for a mask-changing fupd.
      This lemma is intended to be [iApply]ed. *)
  Lemma fupd_mask_intro E1 E2 P :
    E2 ⊆ E1 →
    ((|={E2,E1}=> emp) -∗ P) ⊢ |={E1,E2}=> P.
  Proof.
    intros. etrans; [|by apply fupd_mask_weaken]. by rewrite -fupd_intro.
  Qed.

  Lemma fupd_mask_intro_discard E1 E2 P `{!Absorbing P} :
    E2 ⊆ E1 → P ⊢ |={E1,E2}=> P.
  Proof.
    intros. etrans; [|by apply fupd_mask_intro].
    apply wand_intro_r. rewrite sep_elim_l. done.
  Qed.

  Lemma fupd_frame_l E1 E2 R Q : (R ∗ |={E1,E2}=> Q) ⊢ |={E1,E2}=> R ∗ Q.
  Proof. rewrite !(comm _ R); apply fupd_frame_r. Qed.
  Lemma fupd_wand_l E1 E2 P Q : (P -∗ Q) ∗ (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q.
  Proof. by rewrite fupd_frame_l wand_elim_l. Qed.
  Lemma fupd_wand_r E1 E2 P Q : (|={E1,E2}=> P) ∗ (P -∗ Q) ⊢ |={E1,E2}=> Q.
  Proof. by rewrite fupd_frame_r wand_elim_r. Qed.

  Global Instance fupd_absorbing E1 E2 P :
    Absorbing P → Absorbing (|={E1,E2}=> P).
  Proof. rewrite /Absorbing /bi_absorbingly fupd_frame_l =>-> //. Qed.

  Lemma fupd_trans_frame E1 E2 E3 P Q :
    ((Q ={E2,E3}=∗ emp) ∗ |={E1,E2}=> (Q ∗ P)) ⊢ |={E1,E3}=> P.
  Proof.
    rewrite fupd_frame_l assoc -(comm _ Q) wand_elim_r.
    by rewrite fupd_frame_r left_id fupd_trans.
  Qed.

  Lemma fupd_elim E1 E2 E3 P Q :
    (Q ⊢ (|={E2,E3}=> P)) → (|={E1,E2}=> Q) ⊢ (|={E1,E3}=> P).
  Proof. intros ->. rewrite fupd_trans //. Qed.

  Lemma fupd_mask_frame_r E1 E2 Ef P :
    E1 ## Ef → (|={E1,E2}=> P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P.
  Proof.
    intros ?. rewrite -fupd_mask_frame_r' //. f_equiv.
    apply impl_intro_l, and_elim_r.
  Qed.
  Lemma fupd_mask_mono E1 E2 P : E1 ⊆ E2 → (|={E1}=> P) ⊢ |={E2}=> P.
  Proof.
    intros (Ef&->&?)%subseteq_disjoint_union_L. by apply fupd_mask_frame_r.
  Qed.
  (** How to apply an arbitrary mask-changing view shift when having
      an arbitrary mask. *)
  Lemma fupd_mask_frame E E' E1 E2 P :
    E1 ⊆ E →
    (|={E1,E2}=> |={E2 ∪ (E ∖ E1),E'}=> P) ⊢ (|={E,E'}=> P).
  Proof.
    intros ?. rewrite (fupd_mask_frame_r _ _ (E ∖ E1)); last set_solver.
    rewrite fupd_trans.
    by replace (E1 ∪ E ∖ E1) with E by (by apply union_difference_L).
  Qed.
  (* A variant of [fupd_mask_frame] that works well for accessors: Tailored to
     eliminate updates of the form [|={E1,E1∖E2}=> Q] and provides a way to
     transform the closing view shift instead of letting you prove the same
     side-conditions twice. *)
  Lemma fupd_mask_frame_acc E E' E1(*Eo*) E2(*Em*) P Q :
    E1 ⊆ E →
    (|={E1,E1∖E2}=> Q) -∗
    (Q -∗ |={E∖E2,E'}=> (∀ R, (|={E1∖E2,E1}=> R) -∗ |={E∖E2,E}=> R) -∗  P) -∗
    (|={E,E'}=> P).
  Proof.
    intros HE. apply entails_wand, wand_intro_r. rewrite fupd_frame_r.
    rewrite wand_elim_r. clear Q.
    rewrite -(fupd_mask_frame E E'); first apply fupd_mono; last done.
    (* The most horrible way to apply fupd_intro_mask *)
    rewrite -[X in (X ⊢ _)](right_id emp%I).
    rewrite (fupd_mask_intro_subseteq (E1 ∖ E2 ∪ E ∖ E1) (E ∖ E2) emp); last first.
    { rewrite {1}(union_difference_L _ _ HE). set_solver. }
    rewrite fupd_frame_l fupd_frame_r. apply fupd_elim.
    apply fupd_mono.
    eapply wand_apply;
      last (apply sep_mono; first reflexivity); first reflexivity.
    apply forall_intro=>R. apply wand_intro_r.
    rewrite fupd_frame_r. apply fupd_elim. rewrite left_id.
    rewrite (fupd_mask_frame_r _ _ (E ∖ E1)); last set_solver+.
    rewrite {4}(union_difference_L _ _ HE). done.
  Qed.

  Lemma fupd_mask_subseteq_emptyset_difference E1 E2 :
    E2 ⊆ E1 →
    ⊢@{PROP} |={E1, E2}=> |={∅, E1∖E2}=> emp.
  Proof.
    intros ?. rewrite [in fupd E1](union_difference_L E2 E1); [|done].
    rewrite (comm_L (∪))
      -[X in fupd _ X](left_id_L ∅ (∪) E2) -fupd_mask_frame_r; [|set_solver+].
    apply fupd_mask_intro_subseteq; set_solver.
  Qed.

  Lemma fupd_or E1 E2 P Q :
    (|={E1,E2}=> P) ∨ (|={E1,E2}=> Q) ⊢@{PROP}
    (|={E1,E2}=> (P ∨ Q)).
  Proof. apply or_elim; apply fupd_mono; [ apply or_intro_l | apply or_intro_r ]. Qed.

  Global Instance fupd_or_homomorphism E :
    MonoidHomomorphism bi_or bi_or (flip (⊢)) (fupd (PROP:=PROP) E E).
  Proof. split; [split|]; try apply _; [apply fupd_or | apply fupd_intro]. Qed.

  Lemma fupd_and E1 E2 P Q :
    (|={E1,E2}=> (P ∧ Q)) ⊢@{PROP} (|={E1,E2}=> P) ∧ (|={E1,E2}=> Q).
  Proof. apply and_intro; apply fupd_mono; [apply and_elim_l | apply and_elim_r]. Qed.

  Lemma fupd_exist E1 E2 A (Φ : A → PROP) :
    (∃ x : A, |={E1, E2}=> Φ x) ⊢ |={E1, E2}=> ∃ x : A, Φ x.
  Proof. apply exist_elim=> a. by rewrite -(exist_intro a). Qed.

  Lemma fupd_forall E1 E2 A (Φ : A → PROP) :
    (|={E1, E2}=> ∀ x : A, Φ x) ⊢ ∀ x : A, |={E1, E2}=> Φ x.
  Proof. apply forall_intro=> a. by rewrite -(forall_elim a). Qed.

  Lemma fupd_sep E P Q : (|={E}=> P) ∗ (|={E}=> Q) ⊢ |={E}=> P ∗ Q.
  Proof. by rewrite fupd_frame_r fupd_frame_l fupd_trans. Qed.

  Global Instance fupd_sep_homomorphism E :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (fupd (PROP:=PROP) E E).
  Proof. split; [split|]; try apply _; [apply fupd_sep | apply fupd_intro]. Qed.

  Lemma big_sepL_fupd {A} E (Φ : nat → A → PROP) l :
    ([∗ list] k↦x ∈ l, |={E}=> Φ k x) ⊢ |={E}=> [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepL2_fupd {A B} E (Φ : nat → A → B → PROP) l1 l2 :
    ([∗ list] k↦x;y ∈ l1;l2, |={E}=> Φ k x y) ⊢ |={E}=> [∗ list] k↦x;y ∈ l1;l2, Φ k x y.
  Proof.
    rewrite !big_sepL2_alt !persistent_and_affinely_sep_l.
    etrans; [| by apply fupd_frame_l]. apply sep_mono_r. apply big_sepL_fupd.
  Qed.

  Lemma big_sepM_fupd `{Countable K} {A} E (Φ : K → A → PROP) m :
    ([∗ map] k↦x ∈ m, |={E}=> Φ k x) ⊢ |={E}=> [∗ map] k↦x ∈ m, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepM2_fupd `{Countable K} {A B} E (Φ : K → A → B → PROP) m m' :
    ([∗ map] k↦x;y ∈ m;m', |={E}=> Φ k x y) ⊢ |={E}=> [∗ map] k↦x;y ∈ m;m', Φ k x y.
  Proof.
    rewrite !big_sepM2_alt big_sepM_fupd.
    rewrite !persistent_and_affinely_sep_l fupd_frame_l //.
  Qed.
  Lemma big_sepS_fupd `{Countable A} E (Φ : A → PROP) X :
    ([∗ set] x ∈ X, |={E}=> Φ x) ⊢ |={E}=> [∗ set] x ∈ X, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_fupd `{Countable A} E (Φ : A → PROP) l :
    ([∗ mset] x ∈ l, |={E}=> Φ x) ⊢ |={E}=> [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  (** Fancy updates that take a step derived rules. *)
  Lemma step_fupd_wand Eo Ei P Q : (|={Eo}[Ei]▷=> P) -∗ (P -∗ Q) -∗ |={Eo}[Ei]▷=> Q.
  Proof.
    apply entails_wand, wand_intro_l.
    by rewrite (later_intro (P -∗ Q)) fupd_frame_l -later_sep fupd_frame_l
               wand_elim_l.
  Qed.

  Lemma step_fupd_mask_frame_r Eo Ei Ef P :
    Eo ## Ef → Ei ## Ef → (|={Eo}[Ei]▷=> P) ⊢ |={Eo ∪ Ef}[Ei ∪ Ef]▷=> P.
  Proof.
    intros. rewrite -fupd_mask_frame_r //. do 2 f_equiv. by apply fupd_mask_frame_r.
  Qed.

  Lemma step_fupd_mask_mono Eo1 Eo2 Ei1 Ei2 P :
    Ei2 ⊆ Ei1 → Eo1 ⊆ Eo2 → (|={Eo1}[Ei1]▷=> P) ⊢ |={Eo2}[Ei2]▷=> P.
  Proof.
    intros ??. rewrite -(emp_sep (|={Eo1}[Ei1]▷=> P)%I).
    rewrite (fupd_mask_intro_subseteq Eo2 Eo1 emp) //.
    rewrite fupd_frame_r -(fupd_trans Eo2 Eo1 Ei2). f_equiv.
    rewrite fupd_frame_l -(fupd_trans Eo1 Ei1 Ei2). f_equiv.
    rewrite (fupd_mask_intro_subseteq Ei1 Ei2 (|={_,_}=> emp)) //.
    rewrite fupd_frame_r. f_equiv.
    rewrite [X in (X ∗ _)%I]later_intro -later_sep. f_equiv.
    rewrite fupd_frame_r -(fupd_trans Ei2 Ei1 Eo2). f_equiv.
    rewrite fupd_frame_l -(fupd_trans Ei1 Eo1 Eo2). f_equiv.
    by rewrite fupd_frame_r left_id.
  Qed.

  Lemma step_fupd_intro Ei Eo P : Ei ⊆ Eo → ▷ P ⊢ |={Eo}[Ei]▷=> P.
  Proof. intros. by rewrite -(step_fupd_mask_mono Ei _ Ei _) // -!fupd_intro. Qed.

  Lemma step_fupd_frame_l Eo Ei R Q :
    (R ∗ |={Eo}[Ei]▷=> Q) ⊢ |={Eo}[Ei]▷=> (R ∗ Q).
  Proof.
    rewrite fupd_frame_l.
    apply fupd_mono.
    rewrite [P in P ∗ _ ⊢ _](later_intro R) -later_sep fupd_frame_l.
    by apply later_mono, fupd_mono.
  Qed.

  Lemma step_fupd_fupd Eo Ei P : (|={Eo}[Ei]▷=> P) ⊣⊢ (|={Eo}[Ei]▷=> |={Eo}=> P).
  Proof.
    apply (anti_symm (⊢)).
    - by rewrite -fupd_intro.
    - by rewrite fupd_trans.
  Qed.

  (* [step_fupdN] lemmas *)
  Global Instance step_fupdN_ne Eo Ei n :
    NonExpansive (step_fupdN (PROP:=PROP) Eo Ei n).
  Proof. induction n; solve_proper. Qed.

  Global Instance step_fupdN_proper Eo Ei n :
    Proper ((≡) ==> (≡)) (step_fupdN (PROP:=PROP) Eo Ei n).
  Proof. apply: ne_proper. Qed.

  Lemma step_fupdN_mono Eo Ei n P Q :
    (P ⊢ Q) → (|={Eo}[Ei]▷=>^n P) ⊢ (|={Eo}[Ei]▷=>^n Q).
  Proof. intros. induction n; simpl; repeat (done || f_equiv). Qed.
  Global Instance step_fupdN_mono' Eo Ei n :
    Proper ((⊢) ==> (⊢)) (step_fupdN (PROP:=PROP) Eo Ei n).
  Proof. intros P Q. apply step_fupdN_mono. Qed.
  Global Instance step_fupdN_flip_mono n Eo Ei :
    Proper (flip (⊢) ==> flip (⊢)) (step_fupdN (PROP:=PROP) Eo Ei n).
  Proof. intros P Q. apply step_fupdN_mono. Qed.

  Lemma step_fupdN_0 Eo Ei P : (|={Eo}[Ei]▷=>^0 P) ⊣⊢ P.
  Proof. done. Qed.
  Lemma step_fupdN_succ_l Eo Ei n P :
    (|={Eo}[Ei]▷=>^(S n) P) ⊣⊢ |={Eo}[Ei]▷=> |={Eo}[Ei]▷=>^n P.
  Proof. done. Qed.
  Lemma step_fupdN_succ_r Eo Ei n P :
    (|={Eo}[Ei]▷=>^(S n) P) ⊣⊢ |={Eo}[Ei]▷=>^n |={Eo}[Ei]▷=> P.
  Proof. induction n; simpl; by repeat f_equiv. Qed.
  Lemma step_fupdN_add n m Eo Ei P :
    (|={Eo}[Ei]▷=>^(n+m) P) ⊣⊢ (|={Eo}[Ei]▷=>^n |={Eo}[Ei]▷=>^m P).
  Proof. induction n; simpl; repeat (done || f_equiv). Qed.

  Lemma step_fupdN_wand Eo Ei n P Q :
    (|={Eo}[Ei]▷=>^n P) -∗ (P -∗ Q) -∗ (|={Eo}[Ei]▷=>^n Q).
  Proof.
    apply entails_wand, wand_intro_l. induction n as [|n IH]=> /=.
    { by rewrite wand_elim_l. }
    rewrite -IH -fupd_frame_l later_sep -fupd_frame_l.
    by apply sep_mono; first apply later_intro.
  Qed.

  Lemma step_fupdN_intro Ei Eo n P : Ei ⊆ Eo → ▷^n P ⊢ |={Eo}[Ei]▷=>^n P.
  Proof.
    induction n as [|n IH]=> ?; [done|].
    rewrite /= -step_fupd_intro; [|done]. by rewrite IH.
  Qed.

  Lemma step_fupdN_S_fupd n E P :
    (|={E}[∅]▷=>^(S n) P) ⊣⊢ (|={E}[∅]▷=>^(S n) |={E}=> P).
  Proof.
    apply (anti_symm (⊢)); rewrite !step_fupdN_succ_r -step_fupd_fupd //.
  Qed.

  Lemma step_fupdN_frame_l Eo Ei n R Q :
    (R ∗ |={Eo}[Ei]▷=>^n Q) ⊢ |={Eo}[Ei]▷=>^n (R ∗ Q).
  Proof.
    induction n as [|n IH]; simpl; [done|].
    rewrite step_fupd_frame_l IH //=.
  Qed.

  (** The sidecondition [Ei ⊆ Eo] is needed because for [n = 0],
    this lemma introduces updates in the same way as [step_fupdN_intro]
    (in fact, for [n = 0] it is essentially [step_fupdN_intro], modulo laters). *)
  Lemma step_fupdN_le n m Eo Ei P :
    n ≤ m → Ei ⊆ Eo → (|={Eo}[Ei]▷=>^n P) ⊢ (|={Eo}[Ei]▷=>^m P).
  Proof.
    intros ??. replace m with ((m - n) + n) by lia.
    rewrite step_fupdN_add.
    rewrite -(step_fupdN_intro _ _ (m - n)); last done.
    by rewrite -laterN_intro.
  Qed.

  Section fupd_sbi_derived.
    Context `{!Sbi PROP, !BiFUpdSbi PROP, !BiAffine PROP}.

    Lemma fupd_keep_si_pure {E1 E2} E2' Pi R :
      (|={E1,E2'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E1,E2}=∗ R) ⊢ |={E1,E2}=> R.
    Proof.
      rewrite -{2}(fupd_trans E1 E1 E2) -(fupd_keep_si_pure' E2' Pi).
      by rewrite -fupd_intro.
    Qed.

    Lemma fupd_keep_plainly {E1 E2} E2' P R :
      (|={E1,E2'}=> ■ P) ∧ (P ={E1,E2}=∗ R) ⊢ |={E1,E2}=> R.
    Proof.
      rewrite -{2}(fupd_keep_si_pure E2' (<si_emp_valid> P) R).
      by rewrite {2}si_pure_si_emp_valid_elim.
    Qed.

    Lemma fupd_plainly_later E P : (▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P.
    Proof.
      by rewrite /plainly fupd_si_pure_later si_pure_si_emp_valid_elim.
    Qed.

    Lemma fupd_plainly_forall_2 E {A} (Φ : A → PROP) :
      (∀ x, |={E}=> ■ Φ x) ⊢ |={E}=> ∀ x, Φ x.
    Proof.
      rewrite /plainly fupd_si_pure_forall_2.
      by setoid_rewrite si_pure_si_emp_valid_elim; last apply _.
    Qed.

    Lemma fupd_plainly_mask E E' P : (|={E,E'}=> ■ P) ⊢ |={E}=> P.
    Proof.
      etrans; [|apply (fupd_keep_plainly E' P)]. apply and_intro; [done|].
      apply wand_intro_l. by rewrite sep_elim_l -fupd_intro.
    Qed.

    Lemma fupd_plainly_laterN E n P : (▷^n |={E}=> ■ P) ⊢ |={E}=> ▷^n ◇ P.
    Proof.
      revert P. induction n as [|n IH]=> P /=.
      { by rewrite -except_0_intro plainly_elim. }
      rewrite -!laterN_succ_l !laterN_succ_r.
      rewrite -plainly_idemp fupd_plainly_later.
      by rewrite except_0_plainly_1 later_plainly_1 IH except_0_later.
    Qed.

    (** Laws for general plain propositions. *)
    Lemma fupd_keep_plain {E1 E2} E2' P `{!Plain P} R :
      (|={E1,E2'}=> P) ∧ (P ={E1,E2}=∗ R) ⊢ |={E1,E2}=> R.
    Proof. by rewrite -{1}(plain_plainly P) fupd_keep_plainly. Qed.

    Lemma fupd_plain_mask E E' P `{!Plain P} : (|={E,E'}=> P) ⊢ |={E}=> P.
    Proof. by rewrite {1}(plain P) fupd_plainly_mask. Qed.

    (** This is an alternative version of [fupd_keep_plain] that might look more
    intuitive, but is more annoying to use: we can eliminate a [fupd] that
    "consumes" [R] to produce some plain [P] without actually using up [R]. *)
    Lemma fupd_keep_plain_sep {E} E' P `{!Plain P} R :
      (R ={E,E'}=∗ P) -∗ R -∗ |={E}=> P ∗ R.
    Proof.
      apply entails_wand, wand_intro_r.
      etrans; [|apply (fupd_keep_plain E' P)]. apply and_intro.
      - by rewrite wand_elim_l.
      - rewrite sep_elim_r -fupd_intro. by apply wand_intro_l.
    Qed.

    Lemma fupd_plain_later E P `{!Plain P} : (▷ |={E}=> P) ⊢ |={E}=> ▷ ◇ P.
    Proof. by rewrite {1}(plain P) fupd_plainly_later. Qed.
    Lemma fupd_plain_laterN E n P `{!Plain P} : (▷^n |={E}=> P) ⊢ |={E}=> ▷^n ◇ P.
    Proof. by rewrite {1}(plain P) fupd_plainly_laterN. Qed.

    Lemma fupd_plain_forall_2 E {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      (∀ x, |={E}=> Φ x) ⊢ |={E}=> ∀ x, Φ x.
    Proof.
      rewrite -fupd_plainly_forall_2. apply forall_mono=> x.
      by rewrite {1}(plain (Φ _)).
    Qed.
    Lemma fupd_plain_forall E1 E2 {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      E2 ⊆ E1 →
      (|={E1,E2}=> ∀ x, Φ x) ⊣⊢ (∀ x, |={E1,E2}=> Φ x).
    Proof.
      intros. apply (anti_symm _); first apply fupd_forall.
      trans (∀ x, |={E1}=> Φ x)%I.
      { apply forall_mono=> x. by rewrite fupd_plain_mask. }
      rewrite fupd_plain_forall_2. apply fupd_elim.
      rewrite {1}(plain (∀ x, Φ x)) (fupd_mask_intro_discard E1 E2 (■ _)) //.
      by rewrite plainly_elim.
    Qed.
    Lemma fupd_plain_forall' E {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      (|={E}=> ∀ x, Φ x) ⊣⊢ (∀ x, |={E}=> Φ x).
    Proof. by apply fupd_plain_forall. Qed.

    Lemma step_fupd_plain Eo Ei P `{!Plain P} : (|={Eo}[Ei]▷=> P) ⊢ |={Eo}=> ▷ ◇ P.
    Proof.
      rewrite -(fupd_plain_mask _ Ei (▷ ◇ P)).
      apply fupd_elim. by rewrite fupd_plain_mask -fupd_plain_later.
    Qed.

    Lemma step_fupdN_plain Eo Ei n P `{!Plain P} :
      (|={Eo}[Ei]▷=>^n P) ⊢ |={Eo}=> ▷^n ◇ P.
    Proof.
      induction n as [|n IH]; simpl.
      { by rewrite -fupd_intro -except_0_intro. }
      rewrite step_fupd_fupd IH !fupd_trans /=.
      by rewrite step_fupd_plain except_0_laterN except_0_idemp.
    Qed.

    Lemma step_fupd_plain_forall Eo Ei {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      Ei ⊆ Eo →
      (|={Eo}[Ei]▷=> ∀ x, Φ x) ⊣⊢ (∀ x, |={Eo}[Ei]▷=> Φ x).
    Proof.
      intros. apply (anti_symm _).
      { apply forall_intro=> x. by rewrite (forall_elim x). }
      trans (∀ x, |={Eo}=> ▷ ◇ Φ x)%I.
      { apply forall_mono=> x. by rewrite step_fupd_plain. }
      rewrite -fupd_plain_forall'. apply fupd_elim.
      rewrite -(fupd_except_0 Ei Eo) -step_fupd_intro //.
      by rewrite -later_forall -except_0_forall.
    Qed.
  End fupd_sbi_derived.
End fupd_derived.
