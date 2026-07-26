From stdpp Require Import strings.
From iris.bi Require Import bi plainly big_op.

Unset Mangle Names.
Set Default Proof Using "Type*".

Section tests.
  Context {PROP : bi}.

  (** See https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/610 *)
  Lemma test_impl_persistent_1 `{!Sbi PROP, !BiPersistentlyImplSiPure PROP} :
    Persistent (PROP:=PROP) (True → True).
  Proof. apply _. Qed.
  Lemma test_impl_persistent_2 `{!Sbi PROP, !BiPersistentlyImplSiPure PROP} :
    Persistent (PROP:=PROP) (True → True → True).
  Proof. apply _. Qed.

  (* Test that the right scopes are used. *)
  Lemma test_bi_scope : True.
  Proof.
    (* [<affine> True] is implicitly in %I scope. *)
    pose proof (bi.wand_iff_refl (PROP:=PROP) (<affine> True)).
  Abort.

  (** Rewriting on big ops. *)
  Goal ∀ {l : list nat} {Φ Ψ} {R : PROP},
    (∀ k i, Φ k i ⊢ Ψ k i) → (R ⊢ [∗ list] k↦i ∈ l, Φ k i) →
    R ⊢ [∗ list] k↦i ∈ l, Ψ k i.
  Proof. move=> > H ?. by setoid_rewrite <-H. Qed.
  Goal ∀ {m : gmap nat nat} {Φ Ψ} {R : PROP},
    (∀ k i, Φ k i ⊢ Ψ k i) → (R ⊢ [∗ map] k↦i ∈ m, Φ k i) →
    R ⊢ [∗ map] k↦i ∈ m, Ψ k i.
  Proof. move=> > H ?. by setoid_rewrite <-H. Qed.
  Goal ∀  {m1 m2 : gmap nat nat} {Φ Ψ} {R : PROP},
    (∀ k i j, Φ k i j ⊢ Ψ k i j) → (R ⊢ [∗ map] k↦i;j ∈ m1;m2, Φ k i j) →
    R ⊢ [∗ map] k↦i;j ∈ m1;m2, Ψ k i j.
  Proof. move=> > H ?. by setoid_rewrite <-H. Qed.

  (** Some basic tests to make sure patterns work in big ops. *)
  Definition big_sepM_pattern_value (m : gmap nat (nat * nat)) : PROP :=
    [∗ map] '(x,y) ∈ m, ⌜ 10 = x ⌝.

  Definition big_sepM_pattern_value_tt (m : gmap nat ()) : PROP :=
    [∗ map] '() ∈ m, True.

  Inductive foo := Foo (n : nat).

  Definition big_sepM_pattern_value_custom (m : gmap nat foo) : PROP :=
    [∗ map] '(Foo x) ∈ m, ⌜ 10 = x ⌝.

  Definition big_sepM_pattern_key (m : gmap (nat * nat) nat) : PROP :=
    [∗ map] '(k,_) ↦ _ ∈ m, ⌜ 10 = k ⌝.

  Definition big_sepM_pattern_both (m : gmap (nat * nat) (nat * nat)) : PROP :=
    [∗ map] '(k,_) ↦ '(_,y) ∈ m, ⌜ k = y ⌝.

  Definition big_sepM2_pattern (m1 m2 : gmap nat (nat * nat)) : PROP :=
    [∗ map] '(x,_);'(_,y) ∈ m1;m2, ⌜ x = y ⌝.

  (** This fails, Rocq will infer [x] to have type [Z] due to the equality, and
  then sees a type mismatch with [m : gmap nat nat]. *)
  Fail Definition big_sepM_implicit_type (m : gmap nat nat) : PROP :=
    [∗ map] x ∈ m, ⌜ 10%Z = x ⌝.

  (** With a cast, we can force Rocq to type check the body with [x : nat] and
  thereby insert the [nat] to [Z] coercion in the body. *)
  Definition big_sepM_cast (m : gmap nat nat) : PROP :=
    [∗ map] (x:nat) ∈ m, ⌜ 10%Z = x ⌝.

  Section big_sepM_implicit_type.
    Implicit Types x : nat.

    (** And we can do the same with an [Implicit Type]. *)
    Definition big_sepM_implicit_type (m : gmap nat nat) : PROP :=
      [∗ map] x ∈ m, ⌜ 10%Z = x ⌝.
  End big_sepM_implicit_type.

  Check "big_sepL_simpl".
  Lemma big_sepL_simpl {A} (Φ : A → PROP) :
    ⊢ ([∗ list] x ∈ [], Φ x).
  Proof.
    simpl.
    (* Should [simpl] to [emp] *)
    Show.
  Abort.

  (** This tests that [bupd] is [Typeclasses Opaque]. If [bupd] were transparent,
  Rocq would unify [bupd_instance] with [persistently]. *)
  Goal ∀ (P : PROP),
    ∃ bupd_instance, Persistent (@bupd PROP bupd_instance P).
  Proof. intros. eexists _. Fail apply _. Abort.
  (* Similarly for [plainly], but here it should leave the [Sbi] instance that
  was introduced by [eexists _] unshelved. *)
  Goal ∀ (P : PROP),
    ∃ sbi_instance, Persistent (@plainly PROP sbi_instance P).
  Proof. intros. eexists _. apply _. Unshelve. Abort.

  Section internal_eq_ne.
    Context `{!Sbi PROP} {A : ofe} (a : A).

    Goal NonExpansive (λ x, (a ≡ x : PROP)%I).
    Proof. solve_proper. Qed.

    (* The ones below rely on [SolveProperSubrelation] *)
    Context `{!OfeDiscrete A}.
    Goal NonExpansive (λ x, (⌜a ≡ x⌝ : PROP)%I).
    Proof. solve_proper. Qed.

    Context `{!LeibnizEquiv A}.
    Goal NonExpansive (λ x, (⌜a = x⌝ : PROP)%I).
    Proof. solve_proper. Qed.
  End internal_eq_ne.

  Section instances_for_match.
    Lemma match_persistent :
      Persistent (PROP:=PROP) (∃ b : bool, if b then False else False).
    Proof. apply _. Qed.
    Lemma match_affine :
      Affine (PROP:=PROP) (∃ b : bool, if b then False else False).
    Proof. apply _. Qed.
    Lemma match_absorbing :
      Absorbing (PROP:=PROP) (∃ b : bool, if b then False else False).
    Proof. apply _. Qed.
    Lemma match_timeless :
      Timeless (PROP:=PROP) (∃ b : bool, if b then False else False).
    Proof. apply _. Qed.
    Lemma match_plain `{!Sbi PROP} :
      Plain (PROP:=PROP) (∃ b : bool, if b then False else False).
    Proof. apply _. Qed.

    Lemma match_list_persistent :
      Persistent (PROP:=PROP)
        (∃ l : list nat, match l with [] => False | _ :: _ => False end).
    Proof. apply _. Qed.

    (* From https://gitlab.mpi-sws.org/iris/iris/-/issues/576. *)
    Lemma pair_timeless `{!Timeless (emp%I : PROP)} (m : gset (nat * nat)) :
      Timeless (PROP:=PROP) ([∗ set] '(k1, k2) ∈ m, False).
    Proof. apply _. Qed.

    Check "match_def_unfold_fail".
    (* Don't want instances to unfold def's. *)
    Definition match_foo (b : bool) : PROP := if b then False%I else False%I.
    Lemma match_def_unfold_fail b :
      Persistent (match_foo b).
    Proof. Fail apply _. Abort.
  End instances_for_match.
End tests.
