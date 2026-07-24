From iris.algebra Require Export cmra.
From iris.bi Require Import notation.

(** The type [siProp] defines "plain" step-indexed propositions, on which we
define the usual connectives of higher-order logic, and prove that these satisfy
the usual laws of higher-order logic. *)
Record siProp {SI : sidx} := SiProp {
  siProp_holds : nat → Prop;
  siProp_closed n1 n2 : siProp_holds n1 → n2 ≤ n1 → siProp_holds n2
}.
Local Coercion siProp_holds : siProp >-> Funclass.
Global Arguments SiProp {_}.
Global Arguments siProp_holds : simpl never.
Add Printing Constructor siProp.

Bind Scope bi_scope with siProp.

(** TODO: As part of the migration to Transfinite step-indexing, this file is
ported halfway. We use finite ([nat]-based) step-indexing in the definition of
[siProp], but define a (C)OFE structure for any [SI : sidx]. Hence, [siProp]
remains compatible with the BI laws (we still have [later_exist_false]), which
will change in the future to support the true Transfinite version (for which
[later_exist_false] does not hold).

The function [nat_to_sidx] is used to convert between the internal [nat]s and
the [SI]s in the (C)OFE structure. It is just here temporarily, and will be
removed once the Transfinite migration is complete. *)
Fixpoint nat_to_sidx {SI : sidx} (n : nat) : SI :=
  match n with
  | 0 => 0ᵢ
  | S n => Sᵢ (nat_to_sidx n)
  end.

Lemma nat_to_sidx_mono {SI : sidx} n m :
  n ≤ m → (nat_to_sidx n ≤ nat_to_sidx m)%sidx.
Proof. induction 1; simpl; [done|]. etrans; [done|apply SIdx.le_succ_diag_r]. Qed.

Lemma nat_to_sidx_mono_foo {SI : sidx} n m :
  (nat_to_sidx n ≤ nat_to_sidx m)%sidx → n ≤ m.
Proof.
  revert m. induction n as [|n IH]; [lia|]; intros [|m] Hnm; simpl in *.
  - apply SIdx.le_0_r, SIdx.neq_succ_0 in Hnm as [].
  - apply SIdx.succ_le_mono, IH in Hnm. lia.
Qed.

Global Instance nat_to_sidx_surj `{!SIdxFinite SI} : Surj (=) nat_to_sidx.
Proof.
  intros n. induction (SIdx.lt_wf n) as [n _ IH].
  destruct (finite_index n) as [->|[n' ->]]; first by exists 0.
  destruct (IH n') as [m <-]; first by apply SIdx.lt_succ_diag_r.
  by exists (S m).
Qed.

Section cofe.
  Context {SI : sidx}.

  Inductive siProp_equiv' (P Q : siProp) : Prop :=
    { siProp_in_equiv : ∀ n, P n ↔ Q n }.
  Local Instance siProp_equiv : Equiv siProp := siProp_equiv'.
  Inductive siProp_dist' (n : SI) (P Q : siProp) : Prop :=
    { siProp_in_dist : ∀ n', (nat_to_sidx n' ≤ n)%sidx → P n' ↔ Q n' }.
  Local Instance siProp_dist : Dist siProp := siProp_dist'.
  Definition siProp_ofe_mixin : OfeMixin siProp.
  Proof.
    constructor.
    - intros P Q; split.
      + by intros HPQ n; split=> i ?; apply HPQ.
      + intros HPQ; split=> n. apply HPQ with (nat_to_sidx n); auto.
    - intros n; split.
      + by intros P; split=> i.
      + by intros P Q HPQ; split=> i ?; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i ?.
        by trans (Q i);[apply HP|apply HQ].
    - intros n m P Q HPQ ?. split=> i ?. apply HPQ. by etrans.
  Qed.
  Canonical Structure siPropO : ofe := Ofe siProp siProp_ofe_mixin.

  Program Definition siProp_compl : Compl siPropO := λ c,
    {| siProp_holds n := c (nat_to_sidx n) n |}.
  Next Obligation.
    intros c n1 n2 ??; simpl in *.
    apply (chain_cauchy c (nat_to_sidx n2) (nat_to_sidx n1));
      eauto using siProp_closed, nat_to_sidx_mono.
  Qed.

  Program Definition siProp_lbcompl : LBCompl siPropO := λ n Hn c,
    {| siProp_holds n := c (nat_to_sidx n) _ n |}.
  Next Obligation.
    intros n ? c n'.
    induction n'; simpl; eauto using SIdx.limit_lt_0, SIdx.limit_gt_S.
  Qed.
  Next Obligation.
    intros n ? c n1 n2 ??; simpl in *.
    eapply (bchain_cauchy _ c (nat_to_sidx n2) (nat_to_sidx n1));
      eauto using siProp_closed, nat_to_sidx_mono.
  Qed.

  Global Program Instance siProp_cofe : Cofe siPropO :=
    {| compl := siProp_compl; lbcompl := siProp_lbcompl |}.
  Next Obligation.
    intros n c; split=> n' ?. symmetry.
    apply (chain_cauchy c (nat_to_sidx n')); auto.
  Qed.
  Next Obligation.
    intros n ? c m ?; split=> n' ?. symmetry.
    apply (bchain_cauchy _ c (nat_to_sidx n')); auto.
  Qed.
  Next Obligation.
    intros n ? c1 c2 m Hc; split=> n' ? /=. etrans; [by apply Hc|].
    apply (bchain_cauchy _ c2); auto.
  Qed.
End cofe.

(** [SiProp_downclose] takes a nat-based predicate and turns it into an [siProp]
by closing it off. It is used for [siProp_impl] and [SbiUnfold]. *)
Definition SiProp_downclose {SI : sidx} (Pi : nat → Prop) : siProp :=
  SiProp (λ n, ∀ n', n' ≤ n → Pi n') ltac:(simpl; eauto using Nat.le_trans).

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
  {| siProp_holds n := match n return _ with 0 => True | S n' => P n' end |}.
Next Obligation. intros ? P [|n1] [|n2]; eauto using siProp_closed with lia. Qed.
Local Definition siProp_later_aux : seal (@siProp_later_def). Proof. by eexists. Qed.
Definition siProp_later := unseal siProp_later_aux.
Global Arguments siProp_later {SI}.
Local Definition siProp_later_unseal :
  @siProp_later = @siProp_later_def := seal_eq siProp_later_aux.

Local Program Definition siProp_internal_eq_def
    {SI : sidx} {A : ofe} (a1 a2 : A) : siProp :=
  {| siProp_holds n := a1 ≡{nat_to_sidx n}≡ a2 |}.
Next Obligation.
  intros ?? a1 a2 n1 n2 ? Hn. by eapply dist_le, nat_to_sidx_mono, Hn.
Qed.
Local Definition siProp_internal_eq_aux : seal (@siProp_internal_eq_def). Proof. by eexists. Qed.
Definition siProp_internal_eq := unseal siProp_internal_eq_aux.
Global Arguments siProp_internal_eq {SI A}.
Local Definition siProp_internal_eq_unseal :
  @siProp_internal_eq = @siProp_internal_eq_def := seal_eq siProp_internal_eq_aux.

Local Program Definition siProp_cmra_valid_def
    {SI : sidx} {A : cmra} (a : A) : siProp :=
  {| siProp_holds n := ✓{nat_to_sidx n} a |}.
Next Obligation.
  intros ?? a n1 n2 ? Hn. by eapply cmra_validN_le, nat_to_sidx_mono, Hn.
Qed.
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
    unseal; split; intros HPQ n'' ??; apply HQ, HPQ, HP; auto;
      (etrans; [by apply nat_to_sidx_mono|done]).
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
    unseal; intros n P Q HPQ; split=> -[|n'] //= /SIdx.le_succ_l ?.
    eapply HPQ with (nat_to_sidx n'); auto.
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
  Proof. unseal=> HP; split=>-[|n]; [done|apply HP; eauto using cmra_validN_S]. Qed.
  Lemma later_intro P : P ⊢ ▷ P.
  Proof. unseal; split=> -[|n] /= HP; eauto using siProp_closed. Qed.

  Lemma later_forall_2 {A} (Φ : A → siProp) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
  Proof. unseal; by split=> -[|n]. Qed.
  Lemma later_exist_false {A} (Φ : A → siProp) :
    (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
  Proof. unseal; split=> -[|[|n]] /=; eauto. Qed.
  Lemma later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
  Proof.
    unseal; split=> -[|n] /= HP; [by left|right].
    intros [|n'] ?; eauto using siProp_closed with lia.
  Qed.

  (** Equality *)
  Lemma internal_eq_refl {A : ofe} P (a : A) : P ⊢ (a ≡ a).
  Proof. unseal; by split=> n ? /=. Qed.
  Lemma internal_eq_rewrite {A : ofe} a b (Ψ : A → siProp) :
    NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b.
  Proof.
    intros Hnonexp. unseal; split=> n Hab n' ? HΨ.
    eapply Hnonexp with (nat_to_sidx n) a; auto using nat_to_sidx_mono.
  Qed.

  Lemma prop_ext_2 P Q : ((P → Q) ∧ (Q → P)) ⊢ P ≡ Q.
  Proof.
    unseal; split=> n /= HPQ. split=> n' Hn.
    move: HPQ=> [] /(_ n') ? /(_ n').
    apply nat_to_sidx_mono_foo in Hn. naive_solver.
  Qed.

  Lemma fun_extI {A} {B : A → ofe} (g1 g2 : discrete_fun B) :
    (∀ i, g1 i ≡ g2 i) ⊢ g1 ≡ g2.
  Proof. by unseal. Qed.
  Lemma sig_equivI_1 {A : ofe} (P : A → Prop) (x y : sigO P) :
    proj1_sig x ≡ proj1_sig y ⊢ x ≡ y.
  Proof. by unseal. Qed.

  Lemma later_equivI_1 {A : ofe} (x y : A) : Next x ≡ Next y ⊢ ▷ (x ≡ y).
  Proof.
    unseal. split. intros [|n]; simpl; [done|].
    intros Heq; apply Heq; auto using SIdx.lt_succ_diag_r.
  Qed.
  Lemma later_equivI_2 {A : ofe} (x y : A) : ▷ (x ≡ y) ⊢ Next x ≡ Next y.
  Proof.
    unseal. split. intros n ?; split; intros m Hlt; simpl in *.
    destruct n as [|n]; first by apply SIdx.nlt_0_r in Hlt.
    by eapply dist_le, SIdx.lt_succ_r.
  Qed.

  Lemma discrete_eq_1 {A : ofe} (a b : A) :
    TCOr (Discrete a) (Discrete b) →
    a ≡ b ⊢ ⌜a ≡ b⌝.
  Proof. unseal=> ?. split=> n. by apply (discrete_iff (nat_to_sidx n)). Qed.

  (** TODO: Remove [SIdxFinite] once we use [SI] instead of [nat]. *)
  Lemma internal_eq_entails `{!SIdxFinite SI} {A B : ofe} (a1 a2 : A) (b1 b2 : B) :
    (a1 ≡ a2 ⊢ b1 ≡ b2) ↔ (∀ n, a1 ≡{n}≡ a2 → b1 ≡{n}≡ b2).
  Proof.
    unseal. split.
    - intros [Heq] n. destruct (surj nat_to_sidx n) as [m <-]. apply Heq.
    - intros Heq. split=> n. apply (Heq (nat_to_sidx n)).
  Qed.

  (** Validity *)
  Lemma cmra_valid_intro {A : cmra} P (a : A) : ✓ a → P ⊢ (✓ a).
  Proof. unseal=> ?; split=> n ? /=; by apply cmra_valid_validN. Qed.
  Lemma cmra_valid_elim {A : cmra} (a : A) : ✓ a ⊢ ⌜ ✓{0ᵢ} a ⌝.
  Proof.
    unseal; split=> n ?; by apply cmra_validN_le with (nat_to_sidx n), SIdx.le_0_l.
  Qed.
  Lemma cmra_valid_weaken {A : cmra} (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
  Proof. unseal; split=> n; apply cmra_validN_op_l. Qed.
  (** TODO: Remove [SIdxFinite] once we use [SI] instead of [nat]. *)
  Lemma valid_entails `{!SIdxFinite SI} {A B : cmra} (a : A) (b : B) :
    (✓ a ⊢ ✓ b) ↔ ∀ n, ✓{n} a → ✓{n} b.
  Proof.
    unseal. split.
    - intros [Hv] n. destruct (surj nat_to_sidx n) as [m <-]. apply Hv.
    - intros Hv. split=> n. apply (Hv (nat_to_sidx n)).
  Qed.

  (** Consistency/soundness statements *)
  Lemma pure_soundness φ : (True ⊢ ⌜ φ ⌝) → φ.
  Proof. unseal=> -[H]. by apply (H 0). Qed.
  (** TODO: Remove [SIdxFinite] once we use [SI] instead of [nat]. *)
  Lemma internal_eq_soundness `{!SIdxFinite SI} {A : ofe} (x y : A) :
    (True ⊢ x ≡ y) → x ≡ y.
  Proof.
    unseal=> -[H]. apply equiv_dist=> n.
    destruct (surj nat_to_sidx n) as [m <-]. by apply (H m).
  Qed.
  Lemma later_soundness P : (True ⊢ ▷ P) → (True ⊢ P).
  Proof.
    unseal=> -[HP]; split=> n _. apply siProp_closed with n; last done.
    by apply (HP (S n)).
  Qed.
End primitive.
End siProp_primitive.
