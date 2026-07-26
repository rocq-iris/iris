From iris.algebra Require Import stepindex ofe cmra.

(** * [sidx] instance for [nat] *)
(** This file provides an instantiation of the [sidx] stepindex type for [nat],
called [natSI], which is the stepindex type traditionally used by Iris.

The file also provides variants of (C)OFE and camera lemmas that are specialized
to the [natSI] index type. These restated lemmas use [0], [S], [≤], [<] directly,
so they can be used in combination with [lia], which does not unfold the
projections of the [sidx] class.

Side-effect: every development importing this file will automatically use finite
indices due to the declared instances and canonical structures for [sidx]. The
names of the specialized lemmas shadow the names of the original lemmas. *)

Lemma nat_sidx_mixin : SIdxMixin lt le 0 S.
Proof.
  constructor; try lia.
  - apply _.
  - exact lt_wf.
  - intros m n. destruct (lt_eq_lt_dec m n); naive_solver.
  - intros [|n]; eauto with lia.
Qed.

(** This declares the globally used index type to be [natSI]. All following
lemmas are implicitly specialized to [natSI]! *)
Canonical Structure natSI : sidx := SIdx nat nat_sidx_mixin.
Global Existing Instance natSI | 0.

Global Instance nat_sidx_finite : SIdxFinite natSI.
Proof. intros [|n]; eauto. Qed.

Section finite.
  Local Set Default Proof Using "Type*".

  Lemma dist_later_S {A : ofe} (n : nat) (a b : A) :
    a ≡{n}≡ b ↔ dist_later (S n) a b.
  Proof. apply dist_later_S. Qed.

  Lemma dist_S {A : ofe} n (x y : A) : x ≡{S n}≡ y → x ≡{n}≡ y.
  Proof. apply dist_S. Qed.

  Lemma dist_le {A : ofe} (n m : nat) (x y : A) :
    x ≡{n}≡ y → m ≤ n → x ≡{m}≡ y.
  Proof. by apply dist_le. Qed.

  Lemma contractive_S {A B : ofe} (f : A → B) `{!Contractive f} (n : nat) x y :
    x ≡{n}≡ y → f x ≡{S n}≡ f y.
  Proof. by apply contractive_S. Qed.

  Lemma conv_compl_S `{!Cofe A} n (c : chain A) : compl c ≡{n}≡ c (S n).
  Proof. apply conv_compl_S. Qed.

  Lemma cmra_validN_S {A : cmra} n (x : A) : ✓{S n} x → ✓{n} x.
  Proof. intros ?. by eapply cmra_validN_lt, SIdx.lt_succ_diag_r. Qed.

  Lemma cmra_includedN_S {A : cmra} n (x y : A) : x ≼{S n} y → x ≼{n} y.
  Proof. apply cmra_includedN_S. Qed.

  (** We define [dist_later_fin], an equivalent (see dist_later_fin_iff) version
  of [dist_later] that uses a [match] on the step-index instead of the
  quantification over smaller step-indicies. The definition of [dist_later_fin]
  matches how [dist_later] used to be defined (i.e., with a [match] on the
  step-index), so [dist_later_fin] simplifies adapting existing Iris
  developments that used to rely on the reduction behavior of [dist_later].

  The "fin" indicates that when, in the future, the step-index is abstracted away,
  this equivalence will only hold for finite step-indices (as in, ordinals without
  "limit" steps such as natural numbers). *)

  Definition dist_later_fin {A : ofe} (n : nat) (x y : A) :=
    match n with 0 => True | S n => x ≡{n}≡ y end.

  Lemma dist_later_fin_iff {A : ofe} (n : nat) (x y : A):
    dist_later n x y ↔ dist_later_fin n x y.
  Proof.
    destruct n; unfold dist_later_fin; first by split; eauto using dist_later_0.
    by rewrite dist_later_S.
  Qed.

  (** Shorthands for defining (C)OFEs that only work for [natSI] *)
  Lemma ofe_mixin_finite A `{!Equiv A, !Dist A} :
    (∀ x y : A, x ≡ y ↔ ∀ n, x ≡{n}≡ y) →
    (∀ n, Equivalence (@dist natSI A _ n)) →
    (∀ n (x y : A), x ≡{S n}≡ y → x ≡{n}≡ y) → (* [S] instead of [<] *)
    OfeMixin A.
  Proof. apply ofe_mixin_finite. Qed.

  Definition cofe_finite {A} (compl : Compl A)
      (conv_compl : ∀ n c, compl c ≡{n}≡ c n) : Cofe A :=
    cofe_finite compl conv_compl.
End finite.

(** For backwards compatibility, we define the tactic [f_contractive_fin] that
works with [dist_later_fin] and crucially relies on the step-indices being [nat]
and the reduction behavior of [dist_later_fin].

The tactic [f_contractive_fin] is useful in Iris developments that define custom
notions of [dist] and [dist_later] (e.g., RustBelt), but should be avoided if
possible. *)

(** The tactic [dist_later_fin_intro] is a special case of [dist_later_intro],
which only works for natural numbers as step-indices. It changes [dist_later] to
[dist_later_fin], which only makes sense on natural numbers. We keep
[dist_later_fin_intro] around for backwards compatibility. *)

(** For the goal [dist_later n x y], the tactic [dist_later_fin_intro] changes
the goal to [dist_later_fin] and takes care of the case where [n=0], such
that we are only left with the case where [n = S n'] for some [n']. Changing
[dist_later] to [dist_later_fin] enables reduction and thus works better with
custom versions of [dist] as used e.g. by LambdaRust. *)
Ltac dist_later_fin_intro :=
  match goal with
  | |- @dist_later _ ?A _ ?n ?x ?y =>
      apply dist_later_fin_iff;
      destruct n as [|n]; [exact I|change (@dist natSI A _ n x y)]
  end.
Tactic Notation "f_contractive_fin" :=
  f_contractive_prepare;
  try dist_later_fin_intro;
  try fast_reflexivity.
