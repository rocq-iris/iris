From iris.algebra Require Export cmra.
From iris.bi Require Import notation.
Local Open Scope sidx_scope.

(** The type [siProp] defines "plain" step-indexed propositions, on which we
define the usual connectives of higher-order logic, and prove that these satisfy
the usual laws of higher-order logic. *)
Record siProp {SI : sidx} := SiProp {
  siProp_holds : SI → Prop;
  siProp_closed n1 n2 : siProp_holds n1 → n2 ≤ n1 → siProp_holds n2
}.
Local Coercion siProp_holds : siProp >-> Funclass.
Global Arguments SiProp {_}.
Global Arguments siProp_holds : simpl never.
Add Printing Constructor siProp.

Bind Scope bi_scope with siProp.

Section cofe.
  Context {SI : sidx}.

  Inductive siProp_equiv' (P Q : siProp) : Prop :=
    { siProp_in_equiv : ∀ n, P n ↔ Q n }.
  Local Instance siProp_equiv : Equiv siProp := siProp_equiv'.
  Inductive siProp_dist' (n : SI) (P Q : siProp) : Prop :=
    { siProp_in_dist : ∀ n', n' ≤ n → P n' ↔ Q n' }.
  Local Instance siProp_dist : Dist siProp := siProp_dist'.
  Definition siProp_ofe_mixin : OfeMixin siProp.
  Proof.
    constructor.
    - intros P Q; split.
      + by intros HPQ n; split=> i ?; apply HPQ.
      + intros HPQ; split=> n. apply HPQ with n; auto.
    - intros n; split.
      + by intros P; split=> i.
      + by intros P Q HPQ; split=> i ?; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i ?.
        by trans (Q i); [apply HP|apply HQ].
    - intros n m P Q HPQ ?. split=> i ?. apply HPQ. by etrans.
  Qed.
  Canonical Structure siPropO : ofe := Ofe siProp siProp_ofe_mixin.

  Program Definition siProp_compl : Compl siPropO := λ c,
    {| siProp_holds n := c n n |}.
  Next Obligation.
    intros c n1 n2 ??; simpl in *.
    apply (chain_cauchy c n2 n1); eauto using siProp_closed.
  Qed.

  Program Definition siProp_lbcompl : LBCompl siPropO := λ n Hn c,
    {| siProp_holds n' := ∀ n'' (Hn'' : n'' < n), n'' ≤ n' → c n'' Hn'' n'' |}.
  Next Obligation.
    intros n ? c n1 n2 Hc ? n'' ??; simpl in *. apply Hc. by etrans.
  Qed.

  Global Program Instance siProp_cofe : Cofe siPropO :=
    {| compl := siProp_compl; lbcompl := siProp_lbcompl |}.
  Next Obligation.
    intros n c; split=> n' ?. symmetry.
    apply (chain_cauchy c n'); auto.
  Qed.
  Next Obligation.
    intros n ? c m Hm; split=> n' Hn'. split.
    - intros Hc. by eapply (bchain_cauchy _ c n'),
        (Hc n' (SIdx.le_lt_trans _ _ _ Hn' Hm)).
    - intros Hc n'' ??. eapply (bchain_cauchy _ c n'' m); [by etrans|done|].
      eapply siProp_closed; [apply Hc|]. by etrans.
  Qed.
  Next Obligation.
    intros n ? c1 c2 m Hc; split=> n' ? /=.
    apply forall_proper=> n''. do 2 (apply forall_proper=> ?).
    apply Hc. by etrans.
  Qed.
End cofe.

(** [SiProp_downclose] takes a nat-based predicate and turns it into an [siProp]
by closing it off. It is used for [siProp_impl] and [SbiUnfold]. *)
Program Definition SiProp_downclose {SI : sidx} (Pi : SI → Prop) : siProp :=
  {| siProp_holds n := ∀ n', n' ≤ n → Pi n' |}.
Next Obligation.
  intros ? Pi n1 n2 HPi ? n' ?; simpl in *. apply HPi. by etrans.
Qed.

(** logical entailement *)
Inductive siProp_entails {SI : sidx} (P Q : siProp) : Prop :=
  { siProp_in_entails : ∀ n, P n → Q n }.

(* A small hint DB for local use below. *)
Local Create HintDb siProp_def discriminated.
Global Hint Resolve siProp_closed : siProp_def.

(** logical connectives *)
Local Program Definition siProp_pure_def {SI : sidx} (φ : Prop) : siProp :=
  {| siProp_holds n := φ |}.
Solve Obligations with done.
Local Definition siProp_pure_aux : seal (@siProp_pure_def). Proof. by eexists. Qed.
Definition siProp_pure := unseal siProp_pure_aux.
Global Arguments siProp_pure {SI}.
Local Definition siProp_pure_unseal :
  @siProp_pure = @siProp_pure_def := seal_eq siProp_pure_aux.

Local Program Definition siProp_and_def {SI : sidx} (P Q : siProp) : siProp :=
  {| siProp_holds n := P n ∧ Q n |}.
Solve Obligations with naive_solver eauto 2 with siProp_def.
Local Definition siProp_and_aux : seal (@siProp_and_def). Proof. by eexists. Qed.
Definition siProp_and := unseal siProp_and_aux.
Global Arguments siProp_and {SI}.
Local Definition siProp_and_unseal :
  @siProp_and = @siProp_and_def := seal_eq siProp_and_aux.

Local Program Definition siProp_or_def {SI : sidx} (P Q : siProp) : siProp :=
  {| siProp_holds n := P n ∨ Q n |}.
Solve Obligations with naive_solver eauto 2 with siProp_def.
Local Definition siProp_or_aux : seal (@siProp_or_def). Proof. by eexists. Qed.
Definition siProp_or := unseal siProp_or_aux.
Global Arguments siProp_or {SI}.
Local Definition siProp_or_unseal :
  @siProp_or = @siProp_or_def := seal_eq siProp_or_aux.

Local Program Definition siProp_impl_def {SI : sidx} (P Q : siProp) : siProp :=
  SiProp_downclose (λ n, P n → Q n).
Local Definition siProp_impl_aux : seal (@siProp_impl_def). Proof. by eexists. Qed.
Definition siProp_impl := unseal siProp_impl_aux.
Global Arguments siProp_impl {SI}.
Local Definition siProp_impl_unseal :
  @siProp_impl = @siProp_impl_def := seal_eq siProp_impl_aux.

Local Program Definition siProp_forall_def
    {SI : sidx} {A} (Ψ : A → siProp) : siProp :=
  {| siProp_holds n := ∀ a, Ψ a n |}.
Solve Obligations with naive_solver eauto 2 with siProp_def.
Local Definition siProp_forall_aux : seal (@siProp_forall_def). Proof. by eexists. Qed.
Definition siProp_forall := unseal siProp_forall_aux.
Global Arguments siProp_forall {SI A}.
Local Definition siProp_forall_unseal :
  @siProp_forall = @siProp_forall_def := seal_eq siProp_forall_aux.

Local Program Definition siProp_exist_def
    {SI : sidx} {A} (Ψ : A → siProp) : siProp :=
  {| siProp_holds n := ∃ a, Ψ a n |}.
Solve Obligations with naive_solver eauto 2 with siProp_def.
Local Definition siProp_exist_aux : seal (@siProp_exist_def). Proof. by eexists. Qed.
Definition siProp_exist := unseal siProp_exist_aux.
Global Arguments siProp_exist {SI A}.
Local Definition siProp_exist_unseal :
  @siProp_exist = @siProp_exist_def := seal_eq siProp_exist_aux.

Local Program Definition siProp_later_def {SI : sidx} (P : siProp) : siProp :=
  {| siProp_holds n := ∀ n', n' < n → P n' |}.
Next Obligation.
  intros ? P n1 n2 HP ? n' ?; simpl in *. by eapply HP, SIdx.lt_le_trans.
Qed.
Local Definition siProp_later_aux : seal (@siProp_later_def). Proof. by eexists. Qed.
Definition siProp_later := unseal siProp_later_aux.
Global Arguments siProp_later {SI}.
Local Definition siProp_later_unseal :
  @siProp_later = @siProp_later_def := seal_eq siProp_later_aux.

Local Program Definition siProp_internal_eq_def
    {SI : sidx} {A : ofe} (a1 a2 : A) : siProp :=
  {| siProp_holds n := a1 ≡{n}≡ a2 |}.
Next Obligation. intros ?? a1 a2 n1 n2 ? Hn. by eapply dist_le, Hn. Qed.
Local Definition siProp_internal_eq_aux : seal (@siProp_internal_eq_def).
Proof. by eexists. Qed.
Definition siProp_internal_eq := unseal siProp_internal_eq_aux.
Global Arguments siProp_internal_eq {SI A}.
Local Definition siProp_internal_eq_unseal :
  @siProp_internal_eq = @siProp_internal_eq_def := seal_eq siProp_internal_eq_aux.

Local Program Definition siProp_cmra_valid_def
    {SI : sidx} {A : cmra} (a : A) : siProp :=
  {| siProp_holds n := ✓{n} a |}.
Next Obligation. intros ?? a n1 n2 ? Hn. by eapply cmra_validN_le, Hn. Qed.
Local Definition siProp_cmra_valid_aux : seal (@siProp_cmra_valid_def).
Proof. by eexists. Qed.
Definition siProp_cmra_valid := siProp_cmra_valid_aux.(unseal).
Global Arguments siProp_cmra_valid {SI A}.
Local Definition siProp_cmra_valid_unseal :
  @siProp_cmra_valid = @siProp_cmra_valid_def := siProp_cmra_valid_aux.(seal_eq).

(** Primitive logical rules.
    These are not directly usable later because they do not refer to the BI
    connectives. *)
Module siProp_primitive.
Local Definition siProp_unseal :=
  (siProp_pure_unseal, siProp_and_unseal, siProp_or_unseal,
  siProp_impl_unseal, siProp_forall_unseal, siProp_exist_unseal,
  siProp_later_unseal, siProp_internal_eq_unseal, siProp_cmra_valid_unseal).
Ltac unseal := rewrite !siProp_unseal /=.

Section primitive.
  Local Arguments siProp_holds _ !_ _ /.
  Context {SI : sidx}.

  (** The notations below are implicitly local due to the section, so we do not
  mind the overlap with the general BI notations. *)
  Notation "P ⊢ Q" := (siProp_entails P Q).
  Notation "'True'" := (siProp_pure True) : bi_scope.
  Notation "'False'" := (siProp_pure False) : bi_scope.
  Notation "'⌜' φ '⌝'" := (siProp_pure φ%type%stdpp) : bi_scope.
  Infix "∧" := siProp_and : bi_scope.
  Infix "∨" := siProp_or : bi_scope.
  Infix "→" := siProp_impl : bi_scope.
  Notation "∀ x .. y , P" :=
    (siProp_forall (λ x, .. (siProp_forall (λ y, P%I)) ..)) : bi_scope.
  Notation "∃ x .. y , P" :=
    (siProp_exist (λ x, .. (siProp_exist (λ y, P%I)) ..)) : bi_scope.
  Notation "▷ P" := (siProp_later P) : bi_scope.
  Notation "x ≡ y" := (siProp_internal_eq x y) : bi_scope.
  Notation "✓ x" := (siProp_cmra_valid x) : bi_scope.
  Notation "◇ P" := (▷ False ∨ P)%I : bi_scope.
  Notation "<only0> P" := (▷ False → P)%I : bi_scope.

  (** Below there follow the primitive laws for [siProp]. There are no derived laws
  in this file. *)

  (** Entailment *)
  Lemma entails_po : PreOrder siProp_entails.
  Proof.
    split.
    - intros P; by split=> i.
    - intros P Q Q' HP HQ; split=> i ?; by apply HQ, HP.
  Qed.
  Lemma entails_anti_symm : AntiSymm (≡) siProp_entails.
  Proof. intros P Q HPQ HQP; split=> n; by split; [apply HPQ|apply HQP]. Qed.
  Lemma equiv_entails P Q : (P ≡ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
  Proof.
    split.
    - intros HPQ; split; split=> i; apply HPQ.
    - intros [??]. by apply entails_anti_symm.
  Qed.

  (** Non-expansiveness and setoid morphisms *)
  Lemma pure_ne n : Proper (iff ==> dist n) siProp_pure.
  Proof. intros φ1 φ2 Hφ. by unseal. Qed.
  Lemma and_ne : NonExpansive2 siProp_and.
  Proof.
    intros n P P' HP Q Q' HQ; unseal; split=> n' ?.
    split; (intros [??]; split; [by apply HP|by apply HQ]).
  Qed.
  Lemma or_ne : NonExpansive2 siProp_or.
  Proof.
    intros n P P' HP Q Q' HQ; split=> n' ?.
    unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
  Qed.
  Lemma impl_ne : NonExpansive2 siProp_impl.
  Proof.
    intros n P P' HP Q Q' HQ; split=> n' ?.
    unseal; split; intros HPQ n'' ??;
      apply HQ, HPQ, HP; first [by auto|by etrans].
  Qed.
  Lemma forall_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@siProp_forall _ A).
  Proof.
     by intros Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
  Qed.
  Lemma exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@siProp_exist _ A).
  Proof.
    intros Ψ1 Ψ2 HΨ.
    unseal; split=> n' ?; split; intros [a ?]; exists a; by apply HΨ.
  Qed.
  Lemma later_contractive : Contractive siProp_later.
  Proof.
    unseal; intros n P Q HPQ; split=> -n' ?.
    apply forall_proper=> n''. apply forall_proper=> ?.
    eapply HPQ; last done. by eapply SIdx.lt_le_trans.
  Qed.
  Lemma internal_eq_ne (A : ofe) : NonExpansive2 (@siProp_internal_eq SI A).
  Proof.
    intros n x x' Hx y y' Hy; split=> n' z; unseal; split; intros; simpl in *.
    - rewrite -(dist_le _ _ _ _ Hx) -?(dist_le _ _ _ _ Hy); auto.
    - rewrite (dist_le _ _ _ _ Hx) ?(dist_le _ _ _ _ Hy); auto.
  Qed.
  Lemma cmra_valid_ne (A : cmra) : NonExpansive (@siProp_cmra_valid SI A).
  Proof.
    intros n x x' Hx. unseal; split=> /= n' z.
    by rewrite (dist_le _ _ _ _ Hx).
  Qed.

  (** Introduction and elimination rules *)
  Lemma pure_intro (φ : Prop) P : φ → P ⊢ ⌜ φ ⌝.
  Proof. intros ?. unseal; by split. Qed.
  Lemma pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P.
  Proof. unseal=> HP; split=> n ?. by apply HP. Qed.
  Lemma pure_forall_2 {A} (φ : A → Prop) : (∀ a, ⌜ φ a ⌝) ⊢ ⌜ ∀ a, φ a ⌝.
  Proof. by unseal. Qed.

  Lemma and_elim_l P Q : P ∧ Q ⊢ P.
  Proof. unseal; by split=> n [??]. Qed.
  Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
  Proof. unseal; by split=> n [??]. Qed.
  Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
  Proof.
    intros HQ HR; unseal; split=> n ?.
    split.
    - by apply HQ.
    - by apply HR.
  Qed.

  Lemma or_intro_l P Q : P ⊢ P ∨ Q.
  Proof. unseal; split=> n ?; left; auto. Qed.
  Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
  Proof. unseal; split=> n ?; right; auto. Qed.
  Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
  Proof.
    intros HP HQ. unseal; split=> n [?|?].
    - by apply HP.
    - by apply HQ.
  Qed.

  Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
  Proof.
    unseal=> HQ; split=> n ? n' ??.
    apply HQ; naive_solver eauto using siProp_closed.
  Qed.
  Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
  Proof. unseal=> HP; split=> n [??]. apply HP with n; auto. Qed.

  Lemma forall_intro {A} P (Ψ : A → siProp) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
  Proof. unseal; intros HPΨ; split=> n ? a; by apply HPΨ. Qed.
  Lemma forall_elim {A} {Ψ : A → siProp} a : (∀ a, Ψ a) ⊢ Ψ a.
  Proof. unseal; split=> n HP; apply HP. Qed.

  Lemma exist_intro {A} {Ψ : A → siProp} a : Ψ a ⊢ ∃ a, Ψ a.
  Proof. unseal; split=> n ?; by exists a. Qed.
  Lemma exist_elim {A} (Φ : A → siProp) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
  Proof. unseal; intros HΨ; split=> n [a ?]; by apply HΨ with a. Qed.

  (** Later *)
  Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
  Proof. unseal=> HPQ; split=> n HP n' ?. by apply HPQ, HP. Qed.
  Lemma later_intro P : P ⊢ ▷ P.
  Proof. unseal; split=> n HP n' ?. by eapply siProp_closed, SIdx.lt_le_incl. Qed.

  Lemma later_forall_2 {A} (Φ : A → siProp) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
  Proof. unseal; split=> n HΦ n' ? x. by apply HΦ. Qed.

  Lemma later_exist_except_0 `{!SIdxFinite SI} {A} (Φ : A → siProp) :
    (▷ ∃ a, Φ a) ⊢ ◇ (∃ a, ▷ Φ a).
  Proof.
    unseal; split=> n HΦ; simpl in *. destruct (finite_index n) as [->|[m ->]].
    { left. intros n' []%SIdx.nlt_0_r. }
    right. destruct (HΦ m) as [a HΦa]; first by apply SIdx.lt_succ_diag_r.
    exists a. intros n' ?%SIdx.lt_succ_r. by eapply siProp_closed.
  Qed.

  Lemma only_0_exist_1 {A} (Φ : A → siProp) :
    <only0> (∃ a, Φ a) ⊢ ∃ a, <only0> Φ a.
  Proof.
    unseal; split=> n HΦ; simpl in *.
    destruct (HΦ 0ᵢ) as [a HΦa].
    { apply SIdx.le_0_l. }
    { intros n' []%SIdx.nlt_0_r. }
    exists a. intros n' ? Hn'.
    destruct (decide (n' = 0ᵢ)) as [->|[]%SIdx.neq_0_lt_0%Hn']. done.
  Qed.

  Lemma later_except_0_only_0 P : ▷ P ⊢ ◇ <only0> P.
  Proof.
    unseal; split=> n /= HP. destruct (decide (n = 0ᵢ)) as [->|].
    { left. intros n' []%SIdx.nlt_0_r. }
    right. intros n' ? Hn'.
    destruct (decide (n' = 0ᵢ)) as [->|[]%SIdx.neq_0_lt_0%Hn'].
    by apply HP, SIdx.neq_0_lt_0.
  Qed.

  (** Equality *)
  Lemma internal_eq_refl {A : ofe} P (a : A) : P ⊢ (a ≡ a).
  Proof. unseal; by split=> n ? /=. Qed.
  Lemma internal_eq_rewrite {A : ofe} a b (Ψ : A → siProp) :
    NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b.
  Proof.
    intros Hnonexp. unseal; split=> n Hab n' ? HΨ. apply Hnonexp with n a; auto.
  Qed.

  Lemma prop_ext_2 P Q : ((P → Q) ∧ (Q → P)) ⊢ P ≡ Q.
  Proof. unseal; split=> n /= HPQ. split=> n' Hn. naive_solver. Qed.

  Lemma fun_extI {A} {B : A → ofe} (g1 g2 : discrete_fun B) :
    (∀ i, g1 i ≡ g2 i) ⊢ g1 ≡ g2.
  Proof. by unseal. Qed.
  Lemma sig_equivI_1 {A : ofe} (P : A → Prop) (x y : sigO P) :
    proj1_sig x ≡ proj1_sig y ⊢ x ≡ y.
  Proof. by unseal. Qed.

  Lemma later_equivI_1 {A : ofe} (x y : A) : Next x ≡ Next y ⊢ ▷ (x ≡ y).
  Proof. unseal. split=> n Heq n' ?; simpl in *. by apply Heq. Qed.
  Lemma later_equivI_2 {A : ofe} (x y : A) : ▷ (x ≡ y) ⊢ Next x ≡ Next y.
  Proof. unseal. split=> n Heq; split=> m ?; simpl in *; eauto. Qed.

  Lemma discrete_eq_1 {A : ofe} (a b : A) :
    TCOr (Discrete a) (Discrete b) →
    a ≡ b ⊢ ⌜a ≡ b⌝.
  Proof. unseal=> ?. split=> n. by apply (discrete_iff n). Qed.

  Lemma internal_eq_entails {A B : ofe} (a1 a2 : A) (b1 b2 : B) :
    (a1 ≡ a2 ⊢ b1 ≡ b2) ↔ (∀ n, a1 ≡{n}≡ a2 → b1 ≡{n}≡ b2).
  Proof. unseal. split; intros Heq; [|split=> n]; apply Heq. Qed.

  (** Validity *)
  Lemma cmra_valid_intro {A : cmra} P (a : A) : ✓ a → P ⊢ (✓ a).
  Proof. unseal=> ?; split=> n ? /=; by apply cmra_valid_validN. Qed.
  Lemma cmra_valid_elim {A : cmra} (a : A) : ✓ a ⊢ ⌜ ✓{0ᵢ} a ⌝.
  Proof.
    unseal; split=> n ?; by apply cmra_validN_le with n, SIdx.le_0_l.
  Qed.
  Lemma cmra_valid_weaken {A : cmra} (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
  Proof. unseal; split=> n; apply cmra_validN_op_l. Qed.
  Lemma valid_entails {A B : cmra} (a : A) (b : B) :
    (✓ a ⊢ ✓ b) ↔ ∀ n, ✓{n} a → ✓{n} b.
  Proof. unseal. split; intros Hv; [|split=> n]; apply Hv. Qed.

  (** Consistency/soundness statements *)
  Lemma pure_soundness φ : (True ⊢ ⌜ φ ⌝) → φ.
  Proof. unseal=> -[H]. by apply (H 0ᵢ). Qed.
  Lemma internal_eq_soundness {A : ofe} (x y : A) :
    (True ⊢ x ≡ y) → x ≡ y.
  Proof. unseal=> -[H]. apply equiv_dist=> n. by apply (H n). Qed.
  Lemma later_soundness P : (True ⊢ ▷ P) → (True ⊢ P).
  Proof.
    unseal=> -[HP]; split=> n _. apply siProp_closed with n; last done.
    apply (HP (Sᵢ n)); [done|]. eapply SIdx.lt_succ_diag_r.
  Qed.
End primitive.
End siProp_primitive.
