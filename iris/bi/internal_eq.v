From iris.algebra Require Import excl csum.
From iris.bi Require Export sbi.
From iris.bi Require Import derived_laws_later.

Definition internal_eq {SI : sidx} `{!Sbi PROP} {A : ofe} (a b : A) : PROP :=
  <si_pure> siProp_internal_eq a b.
Global Arguments internal_eq : simpl never.
Global Typeclasses Opaque internal_eq.
Global Instance: Params (@internal_eq) 4 := {}.

Infix "≡" := internal_eq : bi_scope.
Infix "≡@{ A }" := (internal_eq (A := A)) (only parsing) : bi_scope.
Notation "( X ≡.)" := (internal_eq X) (only parsing) : bi_scope.
Notation "(.≡ X )" := (λ Y, Y ≡ X)%I (only parsing) : bi_scope.
Notation "(≡@{ A } )" := (internal_eq (A:=A)) (only parsing) : bi_scope.

(** A smart constructor for [SbiPropExtMixin] that uses the public notion [≡]
instead of the private notion [siProp_internal_eq]. See the documentation about
[SbiPropExtMixin] in [iris.bi.sbi] for more details. *)
Lemma sbi_prop_ext_mixin {SI : sidx} {PROP : bi} `{!SiEmpValid PROP} :
  (∀ P Q : PROP, <si_emp_valid> (P ∗-∗ Q) ⊢@{siPropI} P ≡ Q) →
  SbiPropExtMixin PROP _.
Proof. done. Qed.

Section internal_eq.
  Context {SI : sidx} `{!Sbi PROP}.
  Implicit Types P Q : PROP.

  Local Hint Resolve bi.or_elim bi.or_intro_l' bi.or_intro_r' : core.
  Local Hint Resolve bi.True_intro bi.False_elim : core.
  Local Hint Resolve bi.and_elim_l' bi.and_elim_r' bi.and_intro : core.
  Local Hint Resolve bi.forall_intro : core.
  Local Hint Extern 100 (NonExpansive _) => solve_proper : core.

  (* Force implicit argument PROP *)
  Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
  Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).

  Lemma prop_ext_si_emp_valid_2 P Q : <si_emp_valid> (P ∗-∗ Q) ⊢@{siPropI} P ≡ Q.
  Proof. apply sbi_mixin_prop_ext_si_emp_valid_2, sbi_sbi_prop_ext_mixin. Qed.

  Global Instance internal_eq_ne (A : ofe) :
    NonExpansive2 (@internal_eq _ PROP _ A).
  Proof.
    intros n x x' ? y y' ?. by apply si_pure_ne, siProp_primitive.internal_eq_ne.
  Qed.
  Global Instance internal_eq_proper (A : ofe) :
    Proper ((≡) ==> (≡) ==> (⊣⊢)) (@internal_eq _ PROP _ A).
  Proof. apply (ne_proper_2 _). Qed.

  Lemma internal_eq_refl {A : ofe} P (a : A) : P ⊢ a ≡ a.
  Proof.
    rewrite (bi.True_intro P) -si_pure_pure.
    apply si_pure_mono, siProp_primitive.internal_eq_refl.
  Qed.
  Lemma equiv_internal_eq {A : ofe} P (a b : A) : a ≡ b → P ⊢ a ≡ b.
  Proof. intros ->. apply internal_eq_refl. Qed.
  Lemma pure_internal_eq {A : ofe} (x y : A) : ⌜x ≡ y⌝ ⊢ x ≡ y.
  Proof. apply bi.pure_elim'=> ->. apply internal_eq_refl. Qed.

  Local Hint Resolve equiv_internal_eq : core.

  Lemma internal_eq_rewrite {A : ofe} a b (Ψ : A → PROP) :
    NonExpansive Ψ →
    internal_eq a b ⊢ Ψ a → Ψ b.
  Proof.
    intros. (* [True -∗] makes [True -∗ Ψ a → Ψ a'] persistent, needed for
    [si_pure_si_emp_valid_elim] *)
    pose (Φ a' := (<si_emp_valid> (True -∗ Ψ a → Ψ a'))%I).
    assert (⊢ Φ a) as HΦa.
    { apply si_emp_valid_emp_valid, bi.wand_intro_l.
      by rewrite right_id -bi.entails_impl_True. }
    trans (<si_pure> (Φ a → Φ b) : PROP)%I.
    - apply si_pure_mono. apply siProp_primitive.internal_eq_rewrite.
      solve_proper.
    - unfold bi_emp_valid in HΦa. rewrite -HΦa left_id.
      rewrite /Φ si_pure_si_emp_valid_elim.
      by rewrite -(bi.True_intro emp)%I left_id.
  Qed.
  Lemma internal_eq_rewrite' {A : ofe} a b (Ψ : A → PROP) P :
    NonExpansive Ψ →
    (P ⊢ a ≡ b) → (P ⊢ Ψ a) → P ⊢ Ψ b.
  Proof.
    intros HΨ Heq HΨa. rewrite -(idemp bi_and P) {1}Heq HΨa.
    apply bi.impl_elim_l'. by apply internal_eq_rewrite.
  Qed.

  Lemma internal_eq_sym {A : ofe} (a b : A) : a ≡ b ⊢@{PROP} b ≡ a.
  Proof. apply (internal_eq_rewrite' a b (λ b, b ≡ a)%I); auto. Qed.
  Lemma internal_eq_trans {A : ofe} (a b c : A) : a ≡ b ∧ b ≡ c ⊢ a ≡ c.
  Proof.
    apply (internal_eq_rewrite' b a (λ b, b ≡ c)%I); auto.
    rewrite bi.and_elim_l. apply internal_eq_sym.
  Qed.

  Lemma f_equivI {A B : ofe} (f : A → B) `{!NonExpansive f} x y :
    x ≡ y ⊢ f x ≡ f y.
  Proof. apply (internal_eq_rewrite' x y (λ y, f x ≡ f y)%I); auto. Qed.

  (** Equality of data types *)
  Lemma discrete_eq_1 {A : ofe} (a b : A) :
    TCOr (Discrete a) (Discrete b) →
    a ≡ b ⊢@{PROP} ⌜a ≡ b⌝.
  Proof.
    intros. rewrite -si_pure_pure.
    by apply si_pure_mono, siProp_primitive.discrete_eq_1.
  Qed.
  Lemma discrete_eq {A : ofe} (a b : A) :
    TCOr (Discrete a) (Discrete b) →
    a ≡ b ⊣⊢ ⌜a ≡ b⌝.
  Proof.
    intros. apply (anti_symm _); auto using discrete_eq_1, pure_internal_eq.
  Qed.

  Lemma fun_extI {A} {B : A → ofe} (f g : discrete_fun B) :
    (∀ x, f x ≡ g x) ⊢@{PROP} f ≡ g.
  Proof.
    rewrite /internal_eq -si_pure_forall.
    by apply si_pure_mono, siProp_primitive.fun_extI.
  Qed.
  Lemma sig_equivI_1 {A : ofe} (P : A → Prop) (x y : sig P) :
    `x ≡ `y ⊢@{PROP} x ≡ y.
  Proof. by apply si_pure_mono, siProp_primitive.sig_equivI_1. Qed.

  Lemma prod_equivI {A B : ofe} (x y : A * B) : x ≡ y ⊣⊢ x.1 ≡ y.1 ∧ x.2 ≡ y.2.
  Proof.
    apply (anti_symm _).
    - apply bi.and_intro; apply f_equivI; apply _.
    - rewrite {3}(surjective_pairing x) {3}(surjective_pairing y).
      apply (internal_eq_rewrite' (x.1) (y.1) (λ a, (x.1,x.2) ≡ (a,y.2))%I); auto.
      apply (internal_eq_rewrite' (x.2) (y.2) (λ b, (x.1,x.2) ≡ (x.1,b))%I); auto.
  Qed.
  Lemma sum_equivI {A B : ofe} (x y : A + B) :
    x ≡ y ⊣⊢
      match x, y with
      | inl a, inl a' => a ≡ a' | inr b, inr b' => b ≡ b' | _, _ => False
      end.
  Proof.
    apply (anti_symm _).
    - apply (internal_eq_rewrite' x y (λ y,
               match x, y with
               | inl a, inl a' => a ≡ a' | inr b, inr b' => b ≡ b' | _, _ => False
               end)%I); auto.
      destruct x; auto.
    - destruct x as [a|b], y as [a'|b']; auto; apply f_equivI, _.
  Qed.
  Lemma option_equivI {A : ofe} (x y : option A) :
    x ≡ y ⊣⊢ match x, y with
             | Some a, Some a' => a ≡ a' | None, None => True | _, _ => False
             end.
  Proof.
    apply (anti_symm _).
    - apply (internal_eq_rewrite' x y (λ y,
               match x, y with
               | Some a, Some a' => a ≡ a' | None, None => True | _, _ => False
               end)%I); auto.
      destruct x; auto.
    - destruct x as [a|], y as [a'|]; auto. apply f_equivI, _.
  Qed.

  Lemma csum_equivI {A B : ofe} (sx sy : csum A B) :
    sx ≡ sy ⊣⊢ match sx, sy with
               | Cinl x, Cinl y => x ≡ y
               | Cinr x, Cinr y => x ≡ y
               | CsumInvalid, CsumInvalid => True
               | _, _ => False
               end.
  Proof.
    apply (anti_symm _).
    - apply (internal_eq_rewrite' sx sy (λ sy',
               match sx, sy' with
               | Cinl x, Cinl y => x ≡ y
               | Cinr x, Cinr y => x ≡ y
               | CsumInvalid, CsumInvalid => True
               | _, _ => False
               end)%I); [solve_proper|auto|].
      destruct sx; eauto.
    - destruct sx; destruct sy; eauto;
      apply f_equivI, _.
  Qed.

  Lemma excl_equivI {O : ofe} (x y : excl O) :
    x ≡ y ⊣⊢ match x, y with
             | Excl a, Excl b => a ≡ b
             | ExclInvalid, ExclInvalid => True
             | _, _ => False
             end.
  Proof.
    apply (anti_symm _).
    - apply (internal_eq_rewrite' x y (λ y',
               match x, y' with
               | Excl a, Excl b => a ≡ b
               | ExclInvalid, ExclInvalid => True
               | _, _ => False
               end)%I); [solve_proper|auto|].
      destruct x; eauto.
    - destruct x as [e1|]; destruct y as [e2|]; [|by eauto..].
      apply f_equivI, _.
  Qed.

  Lemma sig_equivI {A : ofe} (P : A → Prop) (x y : sig P) : `x ≡ `y ⊣⊢ x ≡ y.
  Proof.
    apply (anti_symm _).
    - apply sig_equivI_1.
    - apply f_equivI, _.
  Qed.

  Section sigT_equivI.
    Import EqNotations.

    Lemma sigT_equivI {A : Type} {P : A → ofe} (x y : sigT P) :
      x ≡ y ⊣⊢
      ∃ eq : projT1 x = projT1 y, rew eq in projT2 x ≡ projT2 y.
    Proof.
      apply (anti_symm _).
      - apply (internal_eq_rewrite' x y (λ y,
                 ∃ eq : projT1 x = projT1 y, rew eq in projT2 x ≡ projT2 y))%I.
        + move => n [a pa] [b pb] [/=]; intros -> => /= Hab.
          apply bi.exist_ne => ?. by rewrite Hab.
        + done.
        + rewrite -(bi.exist_intro eq_refl) /=. auto.
      - apply bi.exist_elim. move: x y => [a pa] [b pb] /=. intros ->; simpl.
        apply (f_equivI _).
    Qed.
  End sigT_equivI.

  Lemma discrete_fun_equivI {A} {B : A → ofe} (f g : discrete_fun B) :
    f ≡ g ⊣⊢ ∀ x, f x ≡ g x.
  Proof.
    apply (anti_symm _); auto using fun_extI.
    apply (internal_eq_rewrite' f g (λ g, ∀ x : A, f x ≡ g x)%I); auto.
  Qed.
  Lemma ofe_morO_equivI {A B : ofe} (f g : A -n> B) : f ≡ g ⊣⊢ ∀ x, f x ≡ g x.
  Proof.
    apply (anti_symm _).
    - apply (internal_eq_rewrite' f g (λ g, ∀ x : A, f x ≡ g x)%I); auto.
    - rewrite -(discrete_fun_equivI (ofe_mor_car _ _ f) (ofe_mor_car _ _ g)).
      set (h1 (f : A -n> B) :=
        exist (λ f : A -d> B, NonExpansive (f : A → B)) f (ofe_mor_ne A B f)).
      set (h2 (f : sigO (λ f : A -d> B, NonExpansive (f : A → B))) :=
        @OfeMor _ A B (`f) (proj2_sig f)).
      assert (∀ f, h2 (h1 f) = f) as Hh by (by intros []).
      assert (NonExpansive h2) by (intros ??? EQ; apply EQ).
      by rewrite -{2}[f]Hh -{2}[g]Hh -f_equivI -sig_equivI.
  Qed.

  (** Modalities *)
  Lemma absorbingly_internal_eq {A : ofe} (x y : A) : <absorb> (x ≡ y) ⊣⊢ x ≡ y.
  Proof. apply absorbingly_si_pure. Qed.
  Lemma persistently_internal_eq {A : ofe} (a b : A) : <pers> (a ≡ b) ⊣⊢ a ≡ b.
  Proof. apply persistently_si_pure. Qed.

  Global Instance internal_eq_absorbing {A : ofe} (x y : A) :
    Absorbing (PROP:=PROP) (x ≡ y).
  Proof. by rewrite /Absorbing absorbingly_internal_eq. Qed.
  Global Instance internal_eq_persistent {A : ofe} (a b : A) :
    Persistent (PROP:=PROP) (a ≡ b).
  Proof. by intros; rewrite /Persistent persistently_internal_eq. Qed.

  (** Equality under a later. *)
  Lemma later_equivI_1 {A : ofe} (x y : A) : Next x ≡ Next y ⊢@{PROP} ▷ (x ≡ y).
  Proof.
    rewrite /internal_eq -si_pure_later.
    by apply si_pure_mono, siProp_primitive.later_equivI_1.
  Qed.
  Lemma later_equivI_2 {A : ofe} (x y : A) : ▷ (x ≡ y) ⊢@{PROP} Next x ≡ Next y.
  Proof.
    rewrite /internal_eq -si_pure_later.
    by apply si_pure_mono, siProp_primitive.later_equivI_2.
  Qed.
  Lemma later_equivI {A : ofe} (x y : A) : Next x ≡ Next y ⊣⊢ ▷ (x ≡ y).
  Proof. apply (anti_symm _); auto using later_equivI_1, later_equivI_2. Qed.

  Lemma f_equivI_contractive {A B : ofe} (f : A → B) `{Hf : !Contractive f} x y :
    ▷ (x ≡ y) ⊢ f x ≡ f y.
  Proof.
    rewrite later_equivI_2. move: Hf=>/contractive_alt [g [? Hfg]].
    rewrite !Hfg. by apply f_equivI.
  Qed.

  Lemma internal_eq_rewrite_contractive {A : ofe} a b (Ψ : A → PROP) :
    Contractive Ψ →
    ▷ (a ≡ b) ⊢ Ψ a → Ψ b.
  Proof.
    intros. rewrite f_equivI_contractive.
    apply (internal_eq_rewrite (Ψ a) (Ψ b) id _).
  Qed.
  Lemma internal_eq_rewrite_contractive' {A : ofe} a b (Ψ : A → PROP) P :
    Contractive Ψ →
    (P ⊢ ▷ (a ≡ b)) → (P ⊢ Ψ a) → P ⊢ Ψ b.
  Proof.
    intros HΨ Heq HΨa. rewrite -(idemp bi_and P) {1}Heq HΨa.
    apply bi.impl_elim_l'. by apply internal_eq_rewrite_contractive.
  Qed.

  Global Instance eq_timeless {A : ofe} (a b : A) :
    TCOr (Discrete a) (Discrete b) →
    Timeless (PROP:=PROP) (a ≡ b).
  Proof. intros. rewrite /Discrete !discrete_eq. apply (timeless _). Qed.

  (** Equality of propositions *)
  Lemma internal_eq_iff P Q : P ≡ Q ⊢ P ↔ Q.
  Proof.
    apply (internal_eq_rewrite' P Q (λ Q, P ↔ Q))%I; auto using bi.iff_refl.
  Qed.
  Lemma affinely_internal_eq_wand_iff P Q : <affine> (P ≡ Q) ⊢ P ∗-∗ Q.
  Proof.
    apply (internal_eq_rewrite' P Q (λ Q, P ∗-∗ Q))%I; auto.
    - by rewrite bi.affinely_elim.
    - rewrite bi.affinely_elim_emp. apply bi.wand_iff_refl.
  Qed.
  Lemma internal_eq_wand_iff P Q : P ≡ Q ⊢ <absorb> (P ∗-∗ Q).
  Proof.
    rewrite -(bi.persistent_absorbingly_affinely (P ≡ Q)).
    by rewrite affinely_internal_eq_wand_iff.
  Qed.

  Lemma si_pure_internal_eq {A : ofe} (x y : A) : <si_pure> (x ≡ y) ⊣⊢ x ≡ y.
  Proof. done. Qed.

  Lemma prop_ext_si_emp_valid P Q : P ≡ Q ⊣⊢@{siPropI} <si_emp_valid> (P ∗-∗ Q).
  Proof.
    apply (anti_symm _); [|apply prop_ext_si_emp_valid_2].
    rewrite -(@si_pure_entails _ PROP) si_pure_internal_eq.
    apply (internal_eq_rewrite' P Q
      (λ Q, <si_pure> <si_emp_valid> (P ∗-∗ Q)))%I; auto.
    rewrite -bi.wand_iff_refl si_emp_valid_emp si_pure_pure. auto.
  Qed.

  Lemma later_equivI_prop_2 P Q : ▷ (P ≡ Q) ⊢ (▷ P) ≡ (▷ Q).
  Proof.
    rewrite -!si_pure_internal_eq -si_pure_later !prop_ext_si_emp_valid.
    by rewrite -si_emp_valid_later bi.later_wand_iff.
  Qed.

  (** TODO: Remove [SIdxFinite] here and below once we use [SI] instead of [nat] for [siProp]
  in all of the lemmas below. *)
  Lemma internal_eq_soundness `{!SIdxFinite SI} {A : ofe} (x y : A) :
    (⊢@{PROP} x ≡ y) → x ≡ y.
  Proof.
    intros ?%si_pure_emp_valid. by apply siProp_primitive.internal_eq_soundness.
  Qed.

  (** Derive [NonExpansive]/[Contractive] from an internal statement *)
  Lemma internal_eq_entails `{!SIdxFinite SI} {A B : ofe} (a1 a2 : A) (b1 b2 : B) :
    (a1 ≡ a2 ⊢ b1 ≡ b2) ↔ (∀ n, a1 ≡{n}≡ a2 → b1 ≡{n}≡ b2).
  Proof. rewrite si_pure_entails. apply siProp_primitive.internal_eq_entails. Qed.

  Lemma ne_internal_eq `{!SIdxFinite SI} {A B : ofe} (f : A → B) :
    NonExpansive f ↔ ∀ x1 x2, x1 ≡ x2 ⊢ f x1 ≡ f x2.
  Proof.
    split; [apply f_equivI|]. intros Hf n x1 x2. by apply internal_eq_entails.
  Qed.

  Lemma ne_2_internal_eq `{!SIdxFinite SI} {A B C : ofe} (f : A → B → C) :
    NonExpansive2 f ↔ ∀ x1 x2 y1 y2, x1 ≡ x2 ∧ y1 ≡ y2 ⊢ f x1 y1 ≡ f x2 y2.
  Proof.
    split.
    - intros Hf x1 x2 y1 y2.
      change ((x1,y1).1 ≡ (x2,y2).1 ∧ (x1,y1).2 ≡ (x2,y2).2
        ⊢ uncurry f (x1,y1) ≡ uncurry f (x2,y2)).
      rewrite -prod_equivI. apply ne_internal_eq. solve_proper.
    - intros Hf n x1 x2 Hx y1 y2 Hy.
      change (uncurry f (x1,y1) ≡{n}≡ uncurry f (x2,y2)).
      apply ne_internal_eq; [|done].
      intros [??] [??]. rewrite prod_equivI. apply Hf.
  Qed.

  Lemma contractive_internal_eq `{!SIdxFinite SI} {A B : ofe} (f : A → B) :
    Contractive f ↔ ∀ x1 x2, ▷ (x1 ≡ x2) ⊢ f x1 ≡ f x2.
  Proof.
    split; [apply f_equivI_contractive|].
    intros Hf n x1 x2 Hx. specialize (Hf x1 x2).
    rewrite -later_equivI internal_eq_entails in Hf. apply Hf. by f_contractive.
  Qed.

  Global Instance sbi_later_contractive `{!SIdxFinite SI} : BiLaterContractive PROP.
  Proof using Type*.
    rewrite /BiLaterContractive.
    apply contractive_internal_eq, later_equivI_prop_2.
  Qed.

  Lemma only_0_internal_eq `{!SIdxFinite SI} P Q :
    <only0> (P ≡ Q) ⊣⊢@{PROP} <only0> P ≡ <only0> Q.
  Proof.
    rewrite -si_pure_internal_eq prop_ext_si_emp_valid.
    rewrite -si_pure_only_0 -si_emp_valid_only_0 bi.only_0_wand_iff.
    by rewrite -prop_ext_si_emp_valid si_pure_internal_eq.
  Qed.
End internal_eq.
