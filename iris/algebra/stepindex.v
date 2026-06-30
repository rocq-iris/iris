From iris.prelude Require Export prelude.
Set Primitive Projections.

(** Step-Indices

In this file, we declare an interface for step-indices (see [sidx]).
Step-indexing in Iris enables all kinds of recursive constructions such
as mixed-variance recursive definitions and mixed-variance recursive types.
For more information on step-indexing and how it is used in Iris, see the
journal paper "Iris from the Ground Up" (which can be found at
https://doi.org/10.1017/S0956796818000151) or the Iris appendix.

Traditionally, step-indexing is done by using natural numbers as indices.
However, it can also be generalized to richer sets of indices such as ω^2 (i.e.,
pairs of natural numbers with lexicographic ordering), ω^ω (i.e., lists of
natural numbers with lexicographic ordering), countable ordinals, and even
uncountable ordinals. Large parts of Iris are agnostic of the step-indexing type
that is used, which allows us to factor out the notion of a step-index via the
interface of an "index type" (see [sidx] and [SIdxMixin]) and define them
generically in the index type (e.g., the [algebra] folder).

Note that transfinite step-indexing is not a strict improvement on finite
step-indexing (i.e., step-indexing with natural numbers)—they are incomparable
(see the paper on "Transfinite Iris" for an explanation of the trade-offs,
which can be found at https://doi.org/10.1145/3453483.3454031). Thus, to retain
the benefits of both, we make definitions parametric instead of specialized to
natural numbers or a particular type of ordinals. *)

(** An index type [I] comes with
- a well-founded strict linear order [sidx_lt] (written [i < j]),
- a total linear order [sidx_le] (written [i ≤ j]),
- a zero index [sidx_zero] (written [0ᵢ]),
- and a successor operation on indices [sidx_succ] (written [Sᵢ]).

The less-or-equal relation [≤] must be compatible with the less-than relation
[<] ([sidx_mixin_le_lteq]). That is, [i ≤ j] iff [i < j] or [i = j]. The [0ᵢ]
index has to be the smallest step-index (i.e., [¬ i ≺ zero] for all [i]) and the
successor operation [Sᵢ] should yield for a step-index [i] the least index
greater than [i]. The strict order [<] should be _computationally_ decidable,
and, finally, it should be computationally decidable whether a given step-index
is a limit index (i.e., it cannot be reached from any predecessor by applying
the successor operation).

The less-or-equal operation [sidx_le] is not strictly necessary since [i ≤ j]
is equivalent to [i < j] or [i = j]. We add it as an additional parameter to
this interface for engineering reasons: the addition of [sidx_le] simplifies
backwards compatibly to developments that assume step-indices are always natural
numbers and (implicitly) that [(i ≤ j)%sidx] unifies with [(i ≤ j)%nat] for
natural numbers. *)
Record SIdxMixin {I} (ilt ile : relation I) (zero : I) (succ : I → I) := {
  sidx_mixin_lt_trans : Transitive ilt;
  sidx_mixin_lt_wf : well_founded ilt;
  sidx_mixin_lt_trichotomy : TrichotomyT ilt;
  sidx_mixin_le_lteq n m : ile n m ↔ ilt n m ∨ n = m;
  sidx_mixin_nlt_0_r n : ¬ ilt n zero;
  sidx_mixin_lt_succ_diag_r n : ilt n (succ n);
  sidx_mixin_le_succ_l_2 n m : ilt n m → ile (succ n) m;
  (** An index is either a successor or a limit index. The second disjunct in
  [weak_case] considers [0ᵢ] to be a limit index, which is often not desired. So
  typically, instead of [weak_case] you want to use [Index.case] which has an
  explicit disjunct for [0ᵢ] and uses [Index.limit] to define limit indices,
  excluding [0ᵢ]. *)
  sidx_mixin_weak_case n : {m | n = succ m} + (∀ m, ilt m n → ilt (succ m) n);
}.

(** [sidx] is both a canonical structure and a typeclass.
When working with a concrete index type, we usually fix it globally. Declaring
an appropriate instance and structure enables Rocq to infer the globally fixed
index type automatically in almost all places. For an example of how to
instantiate [sidx], see [stepindex_finite.v].

Using both a canonical structure and a type class is not very common. In this
case, it maximizes the inference that is done by Rocq when we use the index type.
The fact that the step-index is a type class makes sure in, for example, lemma
statements that it will be inferred from the context automatically. It also
means that if we work with finite step-indices then the finite step-index
instance will be used by default as soon as we (or any of our dependencies)
import [stepindex_finite.v]. The canonical structure, on the other hand, makes
sure that the index type is inferred automatically as soon as we use either
natural numbers or ordinals as the step-index in a concrete lemma. *)

Structure sidx := SIdx {
  sidx_car :> Type;
  sidx_lt : relation sidx_car;
  sidx_le : relation sidx_car;
  sidx_zero : sidx_car;
  sidx_succ : sidx_car → sidx_car;
  sidx_mixin : SIdxMixin sidx_lt sidx_le sidx_zero sidx_succ;
}.

Existing Class sidx.
Global Arguments SIdx _ {_ _ _ _} _.
Global Arguments sidx_car {_}.
Global Arguments sidx_lt {_}.
Global Arguments sidx_le {_}.
Global Arguments sidx_zero {_}.
Global Arguments sidx_succ {_} _.

Declare Scope sidx_scope.
Delimit Scope sidx_scope with sidx.
Bind Scope sidx_scope with sidx_car.

Local Open Scope sidx_scope.

(** We cannot overload [0] and [S], so we define custom notations with an [i]
subscript. Overloading [0] is disallowed, one should use [Number Notation], but
that only works for "concrete" number types defined as an [Inductive] (not
"abstract" number types represented by a class). One also cannot overload [S]
since it is a constructor (of [nat]) and not a [Notation]. *)
Notation "0ᵢ" := sidx_zero (at level 0).
Notation "'Sᵢ'" := sidx_succ (at level 0).

(** The remaining operations have notations in the `%sidx` scope. *)
Notation "(<)" := sidx_lt (only parsing) : sidx_scope.
Notation "n < m" := (sidx_lt n m) : sidx_scope.

Notation "(≤)" := sidx_le (only parsing) : sidx_scope.
Notation "n ≤ m" := (sidx_le n m) : sidx_scope.

Global Hint Extern 0 (_ ≤ _)%sidx => reflexivity : core.

(** Finite indices are exactly the natural numbers *)
Class SIdxFinite (SI : sidx) :=
  finite_index n : n = 0ᵢ ∨ ∃ m, n = Sᵢ m.

Module SIdx.
Section sidx.
  Context {SI : sidx}.
  Implicit Type n m p : SI.

  (** * Lifting of the mixin properties *)
  (** Not an [Instance], we get that via [StrictOrder]. *)
  Lemma lt_trans : Transitive (<).
  Proof. eapply sidx_mixin_lt_trans, sidx_mixin. Qed.
  Lemma lt_wf : well_founded (<).
  Proof. eapply sidx_mixin_lt_wf, sidx_mixin. Qed.
  Global Instance lt_trichotomy : TrichotomyT (<).
  Proof. eapply sidx_mixin_lt_trichotomy, sidx_mixin. Qed.
  Lemma le_lteq n m : n ≤ m ↔ n < m ∨ n = m.
  Proof. eapply sidx_mixin_le_lteq, sidx_mixin. Qed.
  Lemma nlt_0_r n : ¬ n < 0ᵢ.
  Proof. eapply sidx_mixin_nlt_0_r, sidx_mixin. Qed.
  Lemma lt_succ_diag_r n : n < Sᵢ n.
  Proof. eapply sidx_mixin_lt_succ_diag_r, sidx_mixin. Qed.
  Lemma le_succ_l_2 n m : n < m → Sᵢ n ≤ m.
  Proof. eapply sidx_mixin_le_succ_l_2, sidx_mixin. Qed.
  Lemma weak_case n : { m | n = Sᵢ m } + (∀ m, m < n → Sᵢ m < n).
  Proof. eapply sidx_mixin_weak_case, sidx_mixin. Qed.

  (** * Limit indices *)
  (** [weak_case] allows us to decide whether a number is a limit index.
  However, according to [m < n → Sᵢ m < n] (right disjunct), 0 is a limit
  index. In many definitions and proofs (e.g., [case] and [rec]), it is helpful
  to think of 0 as a special case rather than a degenerate limit index. We
  therefore exclude 0 from the notion of limit indices. *)
  Record limit (n : SI) := Limit {
    limit_gt_S m : m < n → Sᵢ m < n;
    limit_neq_0 : n ≠ 0ᵢ;
  }.

  (** * Derived properties *)
  Global Instance inhabited : Inhabited SI := populate 0ᵢ.

  Global Instance lt_strict : StrictOrder (<).
  Proof.
    split; [|apply lt_trans].
    intros n Hn. induction (lt_wf n) as [n _ IH].
    by apply IH in Hn.
  Qed.

  Global Instance le_po : PartialOrder (≤).
  Proof.
    split; [split|].
    - intros n. apply le_lteq. auto.
    - intros n m p. rewrite /sidx_le. rewrite !le_lteq.
      intros [Hnm|Hnm] [Hmp|Hmp]; subst; [|by eauto..].
      left. by etrans.
    - intros n m [H1| ->]%le_lteq [H2|H2]%le_lteq; [|by eauto..].
      destruct (irreflexivity (<) n). by trans m.
  Qed.

  Lemma lt_le_incl n m : n < m → n ≤ m.
  Proof. intros. apply le_lteq. auto. Qed.
  Local Hint Resolve lt_le_incl : core.

  Global Instance le_total : Total (≤).
  Proof. intros n m. destruct (trichotomy (<) n m); naive_solver. Qed.

  Lemma lt_le_trans n m p : n < m → m ≤ p → n < p.
  Proof. intros ? [| ->]%le_lteq; [|done]. by trans m. Qed.
  Lemma le_lt_trans n m p : n ≤ m → m < p → n < p.
  Proof. intros [| ->]%le_lteq ?; [|done]. by trans m. Qed.

  Lemma le_succ_l n m : Sᵢ n ≤ m ↔ n < m.
  Proof.
    split; [|apply le_succ_l_2].
    intros. eapply lt_le_trans; [|done]. apply lt_succ_diag_r.
  Qed.
  Lemma lt_succ_r n m : n < Sᵢ m ↔ n ≤ m.
  Proof.
    split.
    - intros. destruct (total (≤) n m) as [|[H1| ->]%le_lteq]; eauto.
      destruct (irreflexivity (<) n). eapply lt_le_trans; [done|].
      by apply le_succ_l.
    - intros. eapply le_lt_trans; [done|]. apply lt_succ_diag_r.
  Qed.

  Lemma succ_le_mono n m : n ≤ m ↔ Sᵢ n ≤ Sᵢ m.
  Proof. by rewrite le_succ_l lt_succ_r. Qed.
  Lemma succ_lt_mono n m : n < m ↔ Sᵢ n < Sᵢ m.
  Proof. by rewrite lt_succ_r le_succ_l. Qed.

  Global Instance succ_inj : Inj (=) (=) Sᵢ.
  Proof.
    intros n m Heq.
    apply (anti_symm (≤)); apply succ_le_mono; by rewrite Heq.
  Qed.

  Lemma le_succ_diag_r n : n ≤ Sᵢ n.
  Proof. apply lt_le_incl, lt_succ_diag_r. Qed.

  Lemma neq_0_lt_0 n : n ≠ 0ᵢ ↔ 0ᵢ < n.
  Proof.
    split.
    - destruct (trichotomy (<) 0ᵢ n) as [|[|?%nlt_0_r]]; naive_solver.
    - intros ? ->. by destruct (nlt_0_r 0ᵢ).
  Qed.

  Lemma lt_ge_cases n m : n < m ∨ m ≤ n.
  Proof.
    destruct (trichotomyT (<) n m) as [[| ->]|]; auto using lt_le_incl.
  Qed.
  Lemma le_gt_cases n m : n ≤ m ∨ m < n.
  Proof. destruct (lt_ge_cases m n); auto. Qed.
  Lemma le_ngt n m : n ≤ m ↔ ¬ m < n.
  Proof.
    split.
    - intros ??. apply (irreflexivity (<) n); eauto using le_lt_trans.
    - intros ?. by destruct (lt_ge_cases m n).
  Qed.
  Lemma lt_nge n m : n < m ↔ ¬ m ≤ n.
  Proof.
    split.
    - intros ??. apply (irreflexivity (<) n); eauto using lt_le_trans.
    - intros ?. by destruct (le_gt_cases m n).
  Qed.
  Lemma le_neq n m : n < m ↔ n ≤ m ∧ n ≠ m.
  Proof.
    split.
    - intros. split; [eauto using lt_le_incl|].
      intros ->. by apply (irreflexivity (<) m).
    - intros [? Heq]. apply lt_nge=> ?. by apply Heq, (anti_symm (≤)).
  Qed.

  Lemma nlt_succ_r n m : ¬ m < Sᵢ n ↔ n < m.
  Proof. by rewrite -le_ngt le_succ_l. Qed.

  (** These instances have a very high cost, so that the default instances for
  [nat] are prefered over these ones in case of finite step indexing. *)
  Global Instance eq_dec : EqDecision SI | 1000.
  Proof.
    intros n m. destruct (trichotomyT (<) n m) as [[H| ->]|H].
    - right. intros ->. by apply (irreflexivity (<) m).
    - by left.
    - right. intros ->. by apply (irreflexivity (<) m).
  Qed.

  Global Instance lt_dec : RelDecision (<) | 1000.
  Proof. apply _. Defined.

  Global Instance le_dec : RelDecision (≤) | 1000.
  Proof.
    intros n m. destruct (trichotomyT (<) n m) as [[| ->]|]; [left; by auto..|].
    right. intro. destruct (irreflexivity (<) n); eauto using le_lt_trans.
  Qed.

  Lemma le_0_l n : 0ᵢ ≤ n.
  Proof. apply le_ngt, nlt_0_r. Qed.
  Lemma le_0_r n : n ≤ 0ᵢ ↔ n = 0ᵢ.
  Proof. split; [|by intros ->]. intros. by apply (anti_symm (≤)), le_0_l. Qed.

  Lemma neq_succ_0 n : Sᵢ n ≠ 0ᵢ.
  Proof. apply neq_0_lt_0, lt_succ_r, le_0_l. Qed.

  Lemma succ_neq n : n ≠ Sᵢ n.
  Proof.
    intros Hn. destruct (irreflexivity (<) n). rewrite {2}Hn.
    apply lt_succ_diag_r.
  Qed.

  Lemma limit_0 : ¬limit 0ᵢ.
  Proof. by intros [? []]. Qed.
  Lemma limit_lt_0 n : limit n → 0ᵢ < n.
  Proof. intros. apply neq_0_lt_0; intros ->. by apply limit_0. Qed.

  Lemma limit_S n : ¬limit (Sᵢ n).
  Proof.
    intros [Hlim _]. apply (irreflexivity (<) (Sᵢ n)), Hlim, lt_succ_diag_r.
  Qed.

  Lemma limit_finite `{!SIdxFinite SI} n : ¬limit n.
  Proof.
    destruct (finite_index n) as [->|[m ->]]; auto using limit_0, limit_S.
  Qed.

  Lemma case n : (n = 0ᵢ) + { m | n = Sᵢ m } + limit n.
  Proof.
    destruct (decide (n = 0ᵢ)); [by auto|].
    destruct (weak_case n); by auto using limit.
  Qed.

  (** * Ordinal recursion *)
  (** We define the standard recursion scheme for ordinal induction (i.e.,
  transfinite induction) [rec] with the right "unfolding" lemmas:

    P 0 →
    (∀ i, P i → P (Sᵢ i)) →
    (∀ i, limit i, (∀ j, j < i → P j) → P i) →
    ∀ i, P i *)
  Lemma lt_succ_diag_r' n m : n = Sᵢ m → m < n.
  Proof. intros ->. apply lt_succ_diag_r. Qed.

  Definition rec (P : SI → Type)
      (s : P 0ᵢ)
      (f : ∀ n, P n → P (Sᵢ n))
      (lim : ∀ n, limit n → (∀ m, m < n → P m) → P n) :
      ∀ n, P n :=
    Fix lt_wf _ $ λ n IH,
      match case n with
      | inl (inl EQ) => eq_rect_r P s EQ
      | inl (inr (m ↾ EQ)) => eq_rect_r P (f m (IH m (lt_succ_diag_r' _ _ EQ))) EQ
      | inr Hlim => lim n Hlim IH
      end.

  Definition rec_lim_ext {P : SI → Type}
      (lim : ∀ n, limit n → (∀ m, m < n → P m) → P n) :=
    ∀ n Hn Hn' f g,
      (∀ m Hm, f m Hm = g m Hm) →
      lim n Hn f = lim n Hn' g.

  Lemma rec_unfold P s f lim n :
    rec_lim_ext lim →
    rec P s f lim n =
      match case n with
      | inl (inl EQ) => eq_rect_r P s EQ
      | inl (inr (m ↾ EQ)) => eq_rect_r P (f m (rec P s f lim m)) EQ
      | inr Hlim => lim n Hlim (λ m _, rec P s f lim m)
      end.
  Proof.
    intros Hext. unfold rec at 1. apply Fix_eq=> m g h EQ.
    destruct (case m) as [[?|[m' ->]]|?]; [done| |by auto].
    rewrite /eq_rect_r /= EQ //.
  Qed.

  Lemma rec_zero P s f lim : rec P s f lim 0ᵢ = s.
  Proof.
    rewrite /rec /Fix. destruct (lt_wf 0ᵢ); simpl.
    destruct (case 0ᵢ) as [[H0|[m ?]]|?].
    - by rewrite (proof_irrel H0 (eq_refl _)).
    - by destruct (neq_succ_0 m).
    - by destruct limit_0.
  Qed.

  Lemma rec_succ P s f lim n :
    rec_lim_ext lim →
    rec P s f lim (Sᵢ n) = f n (rec P s f lim n).
  Proof.
    intros Hext. rewrite rec_unfold //.
    destruct (case _) as [[?|[m Hm]]|?].
    - by destruct (neq_succ_0 n).
    - apply (inj _) in Hm as Hm'; subst. by rewrite (proof_irrel Hm (eq_refl _)).
    - by destruct (limit_S n).
  Qed.

  Lemma rec_lim P s f lim n Hn :
    rec_lim_ext lim →
    rec P s f lim n = lim n Hn (λ m _, rec P s f lim m).
  Proof.
    intros Hext. rewrite rec_unfold //.
    destruct (case _) as [[->|[m ->]]|[Hlim H0]].
    - by destruct limit_0.
    - by destruct (limit_S m).
    - by apply Hext.
  Qed.
End sidx.
End SIdx.
