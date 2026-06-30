(** Various lemmas showing that [fixpoint] is closed under the BI properties.
We only prove these lemmas for the unary case; if you need them for an
n-ary function, it is probably easier to copy these proofs than to try and apply
these lemmas via (un)currying. *)
From iris.bi Require Export bi.
From iris.proofmode Require Import proofmode.
Import bi.

Section fixpoint_laws.
  Context {PROP: bi}.
  Implicit Types P Q : PROP.

  Lemma fixpoint_plain `{!Sbi PROP} {A}
      (F : (A -d> PROP) → A -d> PROP) `{!Contractive F} :
    (∀ Φ, (∀ x, Plain (Φ x)) → (∀ x, Plain (F Φ x))) →
    ∀ x, Plain (fixpoint F x).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros Φ1 Φ2 HΦ ??. by rewrite -(HΦ _).
    - exists (λ _, emp%I); apply _.
    - done.
    - apply limit_preserving_forall=> x.
      apply limit_preserving_Plain; solve_proper.
  Qed.

  Lemma fixpoint_persistent {A} (F : (A -d> PROP) → A -d> PROP) `{!Contractive F} :
    (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) →
    ∀ x, Persistent (fixpoint F x).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros Φ1 Φ2 HΦ ??. by rewrite -(HΦ _).
    - exists (λ _, emp%I); apply _.
    - done.
    - apply limit_preserving_forall=> x.
      apply limit_preserving_Persistent; solve_proper.
  Qed.

  Lemma fixpoint_absorbing {A} (F : (A -d> PROP) → A -d> PROP) `{!Contractive F} :
    (∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) →
    ∀ x, Absorbing (fixpoint F x).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros Φ1 Φ2 HΦ ??. by rewrite -(HΦ _).
    - exists (λ _, True%I); apply _.
    - done.
    - apply limit_preserving_forall=> x.
      apply limit_preserving_entails; solve_proper.
  Qed.

  Lemma fixpoint_affine {A} (F : (A -d> PROP) → A -d> PROP) `{!Contractive F} :
    (∀ Φ, (∀ x, Affine (Φ x)) → (∀ x, Affine (F Φ x))) →
    ∀ x, Affine (fixpoint F x).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros Φ1 Φ2 HΦ ??. by rewrite -(HΦ _).
    - exists (λ _, emp%I); apply _.
    - done.
    - apply limit_preserving_forall=> x.
      apply limit_preserving_entails; solve_proper.
  Qed.

  Lemma fixpoint_persistent_absoring {A}
      (F : (A -d> PROP) → A -d> PROP) `{!Contractive F} :
    (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Absorbing (Φ x)) →
          (∀ x, Persistent (F Φ x) ∧ Absorbing (F Φ x))) →
    ∀ x, Persistent (fixpoint F x) ∧ Absorbing (fixpoint F x).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros Φ1 Φ2 HΦ ??. by rewrite -(HΦ _).
    - exists (λ _, True%I); split; apply _.
    - naive_solver.
    - apply limit_preserving_forall=> x.
      apply limit_preserving_and; apply limit_preserving_entails; solve_proper.
  Qed.

  Lemma fixpoint_persistent_affine {A}
      (F : (A -d> PROP) → A -d> PROP) `{!Contractive F} :
    (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Affine (Φ x)) →
          (∀ x, Persistent (F Φ x) ∧ Affine (F Φ x))) →
    ∀ x, Persistent (fixpoint F x) ∧ Affine (fixpoint F x).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros Φ1 Φ2 HΦ ??. by rewrite -(HΦ _).
    - exists (λ _, emp%I); split; apply _.
    - naive_solver.
    - apply limit_preserving_forall=> x.
      apply limit_preserving_and; apply limit_preserving_entails; solve_proper.
  Qed.

  Lemma fixpoint_plain_absoring `{!Sbi PROP} {A}
      (F : (A -d> PROP) → A -d> PROP) `{!Contractive F} :
    (∀ Φ, (∀ x, Plain (Φ x)) → (∀ x, Absorbing (Φ x)) →
          (∀ x, Plain (F Φ x) ∧ Absorbing (F Φ x))) →
    ∀ x, Plain (fixpoint F x) ∧ Absorbing (fixpoint F x).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros Φ1 Φ2 HΦ ??. by rewrite -(HΦ _).
    - exists (λ _, True%I); split; apply _.
    - naive_solver.
    - apply limit_preserving_forall=> x.
      apply limit_preserving_and; apply limit_preserving_entails; solve_proper.
  Qed.

  Lemma fixpoint_plain_affine `{!Sbi PROP} {A}
      (F : (A -d> PROP) → A -d> PROP) `{!Contractive F} :
    (∀ Φ, (∀ x, Plain (Φ x)) → (∀ x, Affine (Φ x)) →
          (∀ x, Plain (F Φ x) ∧ Affine (F Φ x))) →
    ∀ x, Plain (fixpoint F x) ∧ Affine (fixpoint F x).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros Φ1 Φ2 HΦ ??. by rewrite -(HΦ _).
    - exists (λ _, emp%I); split; apply _.
    - naive_solver.
    - apply limit_preserving_forall=> x.
      apply limit_preserving_and; apply limit_preserving_entails; solve_proper.
  Qed.
End fixpoint_laws.
