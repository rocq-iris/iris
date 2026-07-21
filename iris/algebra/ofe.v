From iris.prelude Require Export prelude.
From iris.algebra Require Export stepindex.
Local Set Primitive Projections.

Local Open Scope sidx_scope.

(** This files defines (a shallow embedding of) the category of OFEs: Complete
ordered families of equivalences. This is a cartesian closed category, and
mathematically speaking, the entire development lives in this category. However,
we will generally prefer to work with raw Rocq functions plus some registered
[Proper] instances for non-expansiveness. This makes writing such functions much
easier. It turns out that in many cases, we do not even need non-expansiveness. *)

(** Unbundled version *)
Class Dist {SI : sidx} A := dist : SI → relation A.
Global Hint Mode Dist - ! : typeclass_instances.
Global Instance: Params (@dist) 4 := {}.
Notation "x ≡{ n }≡ y" := (dist n x y)
  (at level 70, n at next level, format "x  ≡{ n }≡  y").
Notation "x ≡{ n }@{ A }≡ y" := (dist (A:=A) n x y)
  (at level 70, n at next level, only parsing).
Notation "(≡{ n }≡)" := (dist n) (only parsing).
Notation "(≡{ n }@{ A }≡)" := (dist (A:=A) n) (only parsing).
Notation "( x ≡{ n }≡.)" := (dist n x) (only parsing).
Notation "(.≡{ n }≡ y )" := (λ x, x ≡{n}≡ y) (only parsing).

Global Hint Extern 0 (_ ≡{_}≡ _) => reflexivity : core.
Global Hint Extern 0 (_ ≡{_}≡ _) => symmetry; assumption : core.
Notation NonExpansive f := (∀ n, Proper (dist n ==> dist n) f).
Notation NonExpansive2 f := (∀ n, Proper (dist n ==> dist n ==> dist n) f).
Notation NonExpansive3 f :=
  (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) f).
Notation NonExpansive4 f :=
  (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n ==> dist n) f).

Tactic Notation "ofe_subst" ident(x) :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H : @dist ?SI ?A ?d ?n x _ |- _ => setoid_subst_aux (@dist SI A d n) x
  | H : @dist ?SI ?A ?d ?n _ x |- _ =>
    symmetry in H; setoid_subst_aux (@dist SI A d n) x
  end.
Tactic Notation "ofe_subst" :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H : @dist ?SI ?A ?d ?n ?x _ |- _ => setoid_subst_aux (@dist SI A d n) x
  | H : @dist ?SI ?A ?d ?n _ ?x |- _ =>
    symmetry in H; setoid_subst_aux (@dist SI A d n) x
  end.

Record OfeMixin {SI : sidx} A `{Equiv A, !Dist A} := {
  mixin_equiv_dist (x y : A) : x ≡ y ↔ ∀ n, x ≡{n}≡ y;
  mixin_dist_equivalence n : Equivalence (@dist SI A _ n);
  mixin_dist_le n m (x y : A) : x ≡{n}≡ y → m ≤ n → x ≡{m}≡ y
}.

(** Bundled version *)
Structure ofe {SI : sidx} := Ofe {
  ofe_car :> Type;
  ofe_equiv : Equiv ofe_car;
  ofe_dist : Dist ofe_car;
  ofe_mixin : OfeMixin ofe_car
}.
Global Arguments Ofe {_} _ {_ _} _.
Add Printing Constructor ofe.
(* FIXME(Rocq #6294) : we need the new unification algorithm here. *)
Global Hint Extern 0 (Equiv _) => refine (ofe_equiv _); shelve : typeclass_instances.
Global Hint Extern 0 (Dist _) => refine (ofe_dist _); shelve : typeclass_instances.
Global Arguments ofe_car : simpl never.
Global Arguments ofe_equiv : simpl never.
Global Arguments ofe_dist : simpl never.
Global Arguments ofe_mixin : simpl never.

(** When declaring instances of subclasses of OFE (like CMRAs and unital CMRAs)
we need Rocq to *infer* the canonical OFE instance of a given type and take the
mixin out of it. This makes sure we do not use two different OFE instances in
different places (see for example the constructors [Cmra] and [Ucmra] in the
file [cmra.v].)

In order to infer the OFE instance, we use the definition [ofe_mixin_of'] which
is inspired by the [clone] trick in ssreflect. It works as follows, when type
checking [@ofe_mixin_of' A ?Ac id] Rocq faces a unification problem:

  ofe_car ?Ac  ~  A

which will resolve [?Ac] to the canonical OFE instance corresponding to [A]. The
definition [@ofe_mixin_of' A ?Ac id] will then provide the corresponding mixin.
Note that type checking of [ofe_mixin_of' A id] will fail when [A] does not have
a canonical OFE instance.

The notation [ofe_mixin_of A] that we define on top of [ofe_mixin_of' A id]
hides the [id] and normalizes the mixin to head normal form. The latter is to
ensure that we do not end up with redundant canonical projections to the mixin,
i.e. them all being of the shape [ofe_mixin_of' A id]. *)
Definition ofe_mixin_of' {SI : sidx} A {Ac : ofe} (f : Ac → A) : OfeMixin Ac := ofe_mixin Ac.
Notation ofe_mixin_of A :=
  ltac:(let H := eval hnf in (ofe_mixin_of' A id) in exact H) (only parsing).

(** Lifting properties from the mixin *)
Section ofe_mixin.
  Context {SI : sidx} {A : ofe}.
  Implicit Types x y : A.

  Lemma equiv_dist x y : x ≡ y ↔ ∀ n, x ≡{n}≡ y.
  Proof. apply (mixin_equiv_dist _ (ofe_mixin A)). Qed.
  Global Instance dist_equivalence n : Equivalence (@dist SI A _ n).
  Proof. apply (mixin_dist_equivalence _ (ofe_mixin A)). Qed.
  Lemma dist_le n m x y : x ≡{n}≡ y → m ≤ n → x ≡{m}≡ y.
  Proof. apply (mixin_dist_le _ (ofe_mixin A)). Qed.
End ofe_mixin.

Global Hint Extern 1 (_ ≡{_}≡ _) => apply equiv_dist; assumption : core.

(** Discrete OFEs and discrete OFE elements *)
Class Discrete {SI : sidx} {A : ofe} (x : A) :=
  discrete_0 y : x ≡{0ᵢ}≡ y → x ≡ y.
Global Arguments discrete_0 {_ _} _ {_} _ _.
Global Hint Mode Discrete - + ! : typeclass_instances.
Global Instance: Params (@Discrete) 2 := {}.

Class OfeDiscrete {SI : sidx} (A : ofe) :=
  #[global] ofe_discrete_discrete (x : A) :: Discrete x.
Global Hint Mode OfeDiscrete - ! : typeclass_instances.

(** OFEs with a completion *)
(** A (converging) "chain" is a sequence of type [A] such that from the n-th
position onwards, everything is n-equal. *)
Record chain {SI : sidx} (A : ofe) := {
  chain_car :> SI → A;
  chain_cauchy n m: n ≤ m → chain_car m ≡{n}≡ chain_car n
}.
Global Arguments chain_car {_ _} _ _.
Global Arguments chain_cauchy {_ _} _ _ _ _.

(** A "bounded chain" up to step index [n] is similar to a "chain", except that
the sequence has length [n], i.e., it is only defined for indices strictly less
than [n]. *)
Record bchain {SI : sidx} (A : ofe) (n : SI) := {
  bchain_car :> ∀ m, m < n → A;
  bchain_cauchy m p Hm Hp : m ≤ p → bchain_car p Hp ≡{m}≡ bchain_car m Hm
}.
Global Arguments bchain_car {_ _} _ _ _.
Global Arguments bchain_cauchy {_ _} _ _ _ _ _.

Program Definition chain_map {SI : sidx} {A B : ofe} (f : A → B)
    `{NonExpansive f} (c : chain A) : chain B :=
  {| chain_car n := f (c n) |}.
Next Obligation. by intros SI A B f Hf c n i ?; apply Hf, chain_cauchy. Qed.

Program Definition bchain_map {SI : sidx} {A B : ofe} (f : A → B)
    `{NonExpansive f} {n} (c : bchain A n) : bchain B n :=
  {| bchain_car m Hm := f (c m Hm) |}.
Next Obligation.
  by intros SI A B f Hf n c m p ? Hm Hp; apply Hf, bchain_cauchy.
Qed.

(** We define a _complete_ OFE, COFE for short. Roughly speaking, the power of
a COFE (over an OFE) is to allow us to compute fixpoints. We want to compute two
different kinds of fixpoints:

1. Fixpoints inside of COFEs. For various kinds of recursive definitions inside
   COFEs (e.g., the Iris weakest precondition or a logical relation with
   recursive types), we want to compute the fixpoint of a function [f : A → A]
   where [A] is a COFE. We can do so if [f] is contractive, using a variant of
   Banach's fixpoint theorem. The construction of this fixpoint is given by
   [fixpoint] below.
2. Fixpoints on COFEs. For step-indexed types in Iris (e.g., [iProp]), we have
   to solve a recursive domain equation on COFEs. The construction of this
   fixpoint for natural numbers as the step-index type is given in
   [cofe_solver.v].

A COFE extends an OFE [A] with two additional operations:

1. [compl: chain A → A], which takes a chain [c] of elements from [A] and maps
   them to a limit element [compl c],
2. [lbcompl: ∀ n, SIdx.limit n → bchain A n → A], which takes a
   bounded chain [c] of elements from [A] and maps them to a limit element
   [lbcompl c]. The chain is bounded in the sense that its domain ranges from
   0 to (but not including) the limit index [n]. (Later we will define
   [bcompl] which completes chains that are bounded by any index, not
   necessarily a limit index.)

We will see the need for the two different limit operations of a COFE below
as part of the [fixpoint] construction. A more detailed explanation can be
found in the Iris Reference and the Transfinite Iris Documentation (see
https://iris-project.org/pdfs/2021-pldi-transfinite-iris-final-appendix.pdf). *)

(** These notations [Compl] and [LBCompl] are convenient to define instances
(e.g., [ofe_mor_compl] without having to repeat the type. The notation [BCompl]
will be used as the type for [bcompl], completing [bchain] with an arbitrary
bound [n]. *)
Notation Compl A := (chain A%type → A).
Notation BCompl A := (∀ n, bchain A%type n → A).
Notation LBCompl A := (∀ n, SIdx.limit n → bchain A%type n → A).

Class Cofe {SI : sidx} (A : ofe) := {
  compl : Compl A;
  lbcompl : LBCompl A;
  conv_compl n c : compl c ≡{n}≡ c n;
  conv_lbcompl {n} Hn (c : bchain A n) {m} Hm : lbcompl n Hn c ≡{m}≡ c m Hm;
  (** The bounded limit operation is non-expansive: for chains agreeing up to
  the limit index, the bounded limits agree *)
  lbcompl_ne n {Hn} (c1 c2 : bchain A n) m :
    (∀ p (Hp : p < n), c1 p Hp ≡{m}≡ c2 p Hp) →
    lbcompl n Hn c1 ≡{m}≡ lbcompl n Hn c2
}.
Global Arguments compl : simpl never.
Global Arguments lbcompl {_ _ _ _} : simpl never.
Global Hint Mode Cofe - ! : typeclass_instances.

Lemma compl_chain_map {SI : sidx} `{!Cofe A, !Cofe B} (f : A → B) c
    `(!NonExpansive f) :
  compl (chain_map f c) ≡ f (compl c).
Proof. apply equiv_dist=>n. by rewrite !conv_compl. Qed.

Program Definition chain_const {SI : sidx} {A : ofe} (a : A) : chain A :=
  {| chain_car n := a |}.
Next Obligation. by intros SI A a n i _. Qed.

Lemma compl_chain_const {SI : sidx} `{!Cofe A} (a : A) :
  compl (chain_const a) ≡ a.
Proof. apply equiv_dist=> n. by rewrite conv_compl. Qed.

Lemma compl_bchain_map {SI : sidx} `{!Cofe A, !Cofe B} (f : A → B)
    n Hn (c : bchain A n) `(!NonExpansive f) m :
  m < n → lbcompl Hn (bchain_map f c) ≡{m}≡ f (lbcompl Hn c).
Proof. intros Hm. by rewrite !(conv_lbcompl _ _ Hm). Qed.

Program Definition bchain_const {SI : sidx} {A : ofe} (a : A) n : bchain A n :=
  {| bchain_car m _ := a |}.
Next Obligation. by intros SI A a n m p Hm Hp Hle. Qed.

Program Definition bchain_le {SI : sidx} `{!Cofe A} {n}
    (c : bchain A n) {m} (Hm : m ≤ n) : bchain A m :=
  {| bchain_car m' Hm' := c m' (SIdx.lt_le_trans _ _ _ Hm' Hm) |}.
Next Obligation.
  intros SI A ? n c m Hm p1 p2 Hp Hp1 Hp2; simpl. by apply (bchain_cauchy n c).
Qed.
Lemma lbcompl_bchain_le {SI : sidx} `{!Cofe A} n Hn m Hm (Hmn : m ≤ n)
    (c : bchain A n) p :
  p < m → lbcompl Hm (bchain_le c Hmn) ≡{p}≡ lbcompl Hn c.
Proof.
  intros Hp. rewrite (conv_lbcompl _ _ Hp).
  rewrite conv_lbcompl. by rewrite /bchain_le /=.
Qed.

(** General properties of OFEs *)
Section ofe.
  Context {SI : sidx} {A : ofe}.
  Implicit Types x y : A.

  Global Instance ofe_equivalence : Equivalence ((≡) : relation A).
  Proof.
    split.
    - by intros x; rewrite equiv_dist.
    - by intros x y; rewrite !equiv_dist.
    - by intros x y z; rewrite !equiv_dist; intros; trans y.
  Qed.
  Global Instance dist_ne n : Proper (dist n ==> dist n ==> iff) (@dist SI A _ n).
  Proof.
    intros x1 x2 ? y1 y2 ?; split; intros.
    - by trans x1; [|trans y1].
    - by trans x2; [|trans y2].
  Qed.
  Global Instance dist_proper n : Proper ((≡) ==> (≡) ==> iff) (@dist SI A _ n).
  Proof.
    by move => x1 x2 /equiv_dist Hx y1 y2 /equiv_dist Hy; rewrite (Hx n) (Hy n).
  Qed.
  Global Instance dist_proper_2 n x : Proper ((≡) ==> iff) (dist n x).
  Proof. by apply dist_proper. Qed.
  Global Instance Discrete_proper : Proper ((≡) ==> iff) (@Discrete SI A).
  Proof. intros x y Hxy. rewrite /Discrete. by setoid_rewrite Hxy. Qed.

  Lemma dist_lt n m x y : x ≡{n}≡ y → m < n → x ≡{m}≡ y.
  Proof. eauto using dist_le, SIdx.lt_le_incl. Qed.
  Lemma dist_le' n n' x y : n' ≤ n → x ≡{n}≡ y → x ≡{n'}≡ y.
  Proof. eauto using dist_le. Qed.
  Lemma dist_S n x y : x ≡{Sᵢ n}≡ y → x ≡{n}≡ y.
  Proof. intros H. eapply dist_lt; eauto using SIdx.lt_succ_diag_r. Qed.

  (** [ne_proper] and [ne_proper_2] are not instances to improve efficiency of
  type class search during setoid rewriting.
  Local Instances of [NonExpansive{,2}] are hence accompanied by instances of
  [Proper] built using these lemmas. *)
  Lemma ne_proper {B : ofe} (f : A → B) `{!NonExpansive f} :
    Proper ((≡) ==> (≡)) f.
  Proof. by intros x1 x2; rewrite !equiv_dist; intros Hx n; rewrite (Hx n). Qed.
  Lemma ne_proper_2 {B C : ofe} (f : A → B → C) `{!NonExpansive2 f} :
    Proper ((≡) ==> (≡) ==> (≡)) f.
  Proof.
     unfold Proper, respectful; setoid_rewrite equiv_dist.
     by intros x1 x2 Hx y1 y2 Hy n; rewrite (Hx n) (Hy n).
  Qed.

  Lemma conv_compl_le `{!Cofe A} n m (c : chain A) : n ≤ m → compl c ≡{n}≡ c m.
  Proof.
    transitivity (c n); first by rewrite conv_compl.
    symmetry. by rewrite chain_cauchy.
  Qed.
  Lemma conv_compl_S `{!Cofe A} n (c : chain A) : compl c ≡{n}≡ c (Sᵢ n).
  Proof. apply conv_compl_le, SIdx.le_succ_diag_r. Qed.

  Lemma discrete_iff n x y `{!TCOr (Discrete x) (Discrete y)} :
    x ≡ y ↔ x ≡{n}≡ y.
  Proof.
    split; intros; [by auto|].
    destruct select (TCOr _ _); [|symmetry];
      apply (discrete_0 _), dist_le with n; eauto using SIdx.le_0_l.
  Qed.
  Lemma discrete_iff_0 n x y `{!TCOr (Discrete x) (Discrete y)} :
    x ≡{0ᵢ}≡ y ↔ x ≡{n}≡ y.
  Proof. by rewrite -!discrete_iff. Qed.
  Lemma discrete n x y `{!TCOr (Discrete x) (Discrete y)} :
    x ≡{n}≡ y → x ≡ y.
  Proof. intros. eapply discrete_iff; done. Qed.

  Global Instance ofe_discrete_subrelation `{!OfeDiscrete A} n :
    @SolveProperSubrelation A (dist n) (≡).
  Proof. intros ???. apply: discrete. done. Qed.
  Global Instance ofe_leibniz_subrelation `{!OfeDiscrete A, !LeibnizEquiv A} n :
    @SolveProperSubrelation A (dist n) (=).
  Proof. intros ?? EQ. unfold_leibniz. apply (is_solve_proper_subrelation EQ). Qed.
End ofe.

(** Contractive functions *)
(** Defined as a record to avoid eager unfolding. *)
Record dist_later {SI : sidx} `{!Dist A} (n : SI) (x y : A) : Prop :=
  { dist_later_lt : ∀ m, m < n → x ≡{m}≡ y }.

Section dist_later.
  Context {SI : sidx} {A : ofe}.
  Implicit Types x y : A.

  Global Instance dist_later_equivalence n : Equivalence (@dist_later SI A _ n).
  Proof.
    split.
    - intros ?; by split.
    - intros ?? [H]; split; intros ??; by rewrite H.
    - intros ??? [H1] [H2]; split; intros ??; by rewrite H1 ?H2.
  Qed.

  Lemma dist_dist_later n x y : dist n x y → dist_later n x y.
  Proof. intros. split; eauto using dist_lt. Qed.

  Lemma dist_later_dist_lt n m (x y : A) : m < n → dist_later n x y → dist m x y.
  Proof. intros ? H; by apply H. Qed.

  Lemma dist_later_0 x y : dist_later 0ᵢ x y.
  Proof. split. intros ? []%SIdx.nlt_0_r. Qed.

  Lemma dist_later_S n x y : x ≡{n}≡ y ↔ dist_later (Sᵢ n) x y.
  Proof.
    split.
    - intros Hn; split; intros m Hm%SIdx.lt_succ_r. by eapply dist_le.
    - intros Hdist. by apply Hdist, SIdx.lt_succ_r.
  Qed.
End dist_later.

(* We don't actually need this lemma (as our tactics deal with this through
   other means), but technically speaking, this is the reason why
   pre-composing a non-expansive function to a contractive function
   preserves contractivity. *)
Lemma ne_dist_later {SI : sidx} {A B : ofe} (f : A → B) :
  NonExpansive f → ∀ n, Proper (dist_later n ==> dist_later n) f.
Proof. intros Hf ??? [H]; split; intros ??; by eapply Hf, H. Qed.

Notation Contractive f := (∀ n, Proper (dist_later n ==> dist n) f).

Global Instance const_contractive {SI : sidx} {A B : ofe} (x : A) :
  Contractive (@const A B x).
Proof. by intros n y1 y2. Qed.

Section contractive.
  Local Set Default Proof Using "Type*".
  Context {SI : sidx} {A B : ofe} (f : A → B) `{!Contractive f}.
  Implicit Types x y : A.

  Lemma contractive_0 x y : f x ≡{0ᵢ}≡ f y.
  Proof. by apply (_ : Contractive f), dist_later_0. Qed.
  Lemma contractive_dist_later_dist n x y : dist_later n x y → f x ≡{n}≡ f y.
  Proof. by apply (_ : Contractive f). Qed.
  Lemma contractive_S n x y : x ≡{n}≡ y → f x ≡{Sᵢ n}≡ f y.
  Proof. intros. by apply contractive_dist_later_dist, dist_later_S. Qed.

  Global Instance contractive_ne : NonExpansive f | 100.
  Proof.
    intros n x y ?; eapply (dist_lt (Sᵢ n)), SIdx.lt_succ_diag_r.
    eapply contractive_dist_later_dist. split.
    intros ??%SIdx.lt_succ_r. by eapply dist_le.
  Qed.

  Global Instance contractive_proper : Proper ((≡) ==> (≡)) f | 100.
  Proof. apply (ne_proper _). Qed.
End contractive.

Lemma dist_pointwise_lt {SI : sidx} {A} {B : ofe} n m (f g : A → B):
  m < n →
  pointwise_relation A (dist_later n) f g →
  pointwise_relation A (dist m) f g.
Proof. intros Hlt Hp a. by apply Hp. Qed.

(** The tactic [f_contractive] can be used to prove contractiveness or
non-expansiveness of a function [f]. Inside of the proof of
contractiveness/non-expansiveness, if the current goal is
  [g x1 ... xn ≡{i}≡ g y1 ... yn]
for a contractive function [g] (that is used inside of the body of [f]),
then the tactic will try to find a suitable [Contractive] instance for [g]
and apply it. Currently, the tactic only supports one (i.e., [n = 1]) and
two (i.e., [n = 2]) arguments. As a result of applying the [Contractive]
instance for [g], one of the goals will be [dist_later i xi yi] and the tactic
will try to simplify or solve the goal. By simplify we mean that it will
turn hypotheses [dist_later] into [dist].

The tactic [f_contractive] is implemented using

1. [f_contractive_prepare] which looks up a [Contractive] looks at which
   function is being applied on both sides of a [dist], looks up the
   [Contractive] instance (or the equivalent for two arguments) and applies it.
2. [dist_later_intro] introduces the resulting goals with [dist_later n x y]. *)
Ltac f_contractive_prepare :=
  match goal with
  | |- ?f _ ≡{_}≡ ?f _ => simple apply (_ : Proper (dist_later _ ==> dist _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => simple apply (_ : Proper (dist_later _ ==> _ ==> dist _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => simple apply (_ : Proper (_ ==> dist_later _ ==> dist _) f)
  end.

(** For the goal [dist_later n x y], the tactic [dist_later_intro as m Hm]
introduces a smaller step-index [Hm : m < n] and tries to lower assumptions in
the context to [m] where possible. The arguments [m] and [Hm] can be omitted,
in which case a fresh identifier is used. *)
Tactic Notation "dist_later_intro" "as" ident(idxName) ident(ltName) :=
  match goal with
  | |- dist_later ?n ?x ?y =>
      constructor; intros idxName ltName;
      repeat match goal with
      | H: dist_later n _ _ |- _ => destruct H as [H]; specialize (H idxName ltName) as H
      | H: pointwise_relation _ (dist_later n) _ _ |- _ =>
         apply (dist_pointwise_lt _ idxName _ _ ltName) in H
      end
  end.
Tactic Notation "dist_later_intro" :=
  let m := fresh "m" in
  let Hlt := fresh "Hlt" in
  dist_later_intro as m Hlt.

(** We combine [f_contractive_prepare] and [dist_later_intro] into the
[f_contractive] tactic.

For all the goals not solved by [dist_later_intro] (i.e., the ones that are
not [dist_later n x y]), we try reflexivity. Since reflexivity can be very
expensive when unification fails, we use [fast_reflexivity]. *)

Tactic Notation "f_contractive" "as" ident(idxName) ident(ltName) :=
  f_contractive_prepare;
  try dist_later_intro as idxName ltName;
  try fast_reflexivity.

Tactic Notation "f_contractive" :=
  let m := fresh "m" in
  let Hlt := fresh "Hlt" in
  f_contractive as m Hlt.

Ltac solve_contractive :=
  solve_proper_core ltac:(fun _ => first [f_contractive | f_equiv]).

(** Limit preserving predicates *)
(** To perform induction over a fixpoint ([fixpoint_ind]) and to construct the
COFE over a Sigma type ([sig_cofe]) we need the predicate to be limit
preserving: if it holds for every element of a chain, it must hold for the
limit. *)
Class LimitPreserving {SI : sidx} `{!Cofe A} (P : A → Prop) : Prop := {
  limit_preserving_compl (c : chain A) :
    (∀ n, P (c n)) → P (compl c);
  limit_preserving_lbcompl n Hn (c : bchain A n) :
    (∀ m Hm, P (c m Hm)) → P (lbcompl Hn c);
}.
Global Hint Mode LimitPreserving - + + ! : typeclass_instances.

Section limit_preserving.
  Context {SI : sidx} `{!Cofe A}.
  Implicit Types P Q : A → Prop.

  (* These lemmas are not instances as they will never fire automatically...
  but they can still be helpful in proving things to be limit preserving. *)

  Lemma limit_preserving_sidx_finite `{!SIdxFinite SI} P :
    LimitPreserving P ↔ ∀ c : chain A, (∀ n, P (c n)) → P (compl c).
  Proof.
    split; [by destruct 1|]. intros Hcompl. split; [done|].
    intros n Hn. by destruct (SIdx.limit_finite n).
  Qed.

  Lemma limit_preserving_ext (P Q : A → Prop) :
    (∀ x, P x ↔ Q x) → LimitPreserving P → LimitPreserving Q.
  Proof.
    intros HP [Hcompl Hlbcompl]. split.
    - intros c ?. apply HP, Hcompl=> n; by apply HP.
    - intros n Hn c HC. apply HP, Hlbcompl=> m Hm. by apply HP.
  Qed.

  Global Instance limit_preserving_const (P : Prop) : LimitPreserving (λ _ : A, P).
  Proof.
    split.
    - intros c HP. apply (HP 0ᵢ).
    - intros n [Hlim Hn] Hc HP. by apply (HP (Sᵢ 0ᵢ)), Hlim, SIdx.neq_0_lt_0.
  Qed.

  Lemma limit_preserving_discrete P :
    Proper (dist 0ᵢ ==> impl) P → LimitPreserving P.
  Proof.
    intros HP. split.
    - intros c Hc. by rewrite (conv_compl 0ᵢ).
    - intros n Hn c HPc.
      rewrite (conv_lbcompl _ _ (SIdx.limit_lt_0 _ Hn)). apply HPc.
  Qed.

  Lemma limit_preserving_and P1 P2 :
    LimitPreserving P1 →
    LimitPreserving P2 →
    LimitPreserving (λ x, P1 x ∧ P2 x).
  Proof.
    intros [Hcompl1 Hlbcompl1] [Hcompl2 Hlbcompl2]. split.
    - intros c Hc. split; [apply Hcompl1|apply Hcompl2]; apply Hc.
    - intros n Hn c Hc. split; [apply Hlbcompl1|apply Hlbcompl2]; apply Hc.
  Qed.

  Lemma limit_preserving_impl P1 P2 :
    Proper (dist 0ᵢ ==> impl) P1 →
    LimitPreserving P2 →
    LimitPreserving (λ x, P1 x → P2 x).
  Proof.
    intros HP1 [Hcompl Hlbcompl]. split.
    - intros c Hc HP1c. apply Hcompl=> n. eapply Hc, HP1, HP1c.
      apply dist_le with n, SIdx.le_0_l. apply conv_compl.
    - intros n Hn c Hc HP1c. apply Hlbcompl=> m Hm. eapply Hc, HP1, HP1c.
      apply dist_le with m, SIdx.le_0_l. apply conv_lbcompl.
  Qed.

  (** This is strictly weaker than the [_impl] variant, but sometimes automation
  is better at proving [Proper] for [iff] than for [impl]. *)
  Lemma limit_preserving_impl' P1 P2 :
    Proper (dist 0ᵢ ==> iff) P1 →
    LimitPreserving P2 →
    LimitPreserving (λ x, P1 x → P2 x).
  Proof.
    intros HP1. apply limit_preserving_impl. intros ???.
    apply iff_impl_subrelation. by apply HP1.
  Qed.

  Lemma limit_preserving_forall {B} (P : B → A → Prop) :
    (∀ y, LimitPreserving (P y)) →
    LimitPreserving (λ x, ∀ y, P y x).
  Proof.
    intros Hlim. split.
    - intros c Hc y. by apply Hlim.
    - intros n Hn c Hc y. by apply Hlim.
  Qed.

  (** We need [SIdxFinite] because [compl_bchain_map] does not hold for [≡],
  only for a bounded [≡{m}≡]. *)
  Lemma limit_preserving_equiv `{!SIdxFinite SI} `{!Cofe B} (f g : A → B) :
    NonExpansive f → NonExpansive g → LimitPreserving (λ x, f x ≡ g x).
  Proof.
    intros Hf Hg. apply limit_preserving_sidx_finite=> c Hfg.
    apply equiv_dist=> n. by rewrite -!compl_chain_map !conv_compl /= Hfg.
  Qed.
End limit_preserving.

(** Fixpoint *)
(** A COFE defines a limit operation [lbcompl] for all limit indices. When
defining a fixpoint operator on COFEs, it is convenient
to have a limit operation which can be applied to every index, instead of just
the limit indices. We derive such an operation, called [bcompl] for
"bounded completion". *)

Section bcompl.
  Context {SI : sidx} `{!Cofe A, !Inhabited A}.

  Definition bcompl : BCompl A := λ n c,
    match SIdx.case n with
    | inl (inl Hn') => inhabitant
    (* If the chain ends in a non-zero non-limit ordinal, we can just take the
    last element as the limit. *)
    | inl (inr (m ↾ Hm)) => c m (SIdx.lt_succ_diag_r' _ _ Hm)
    | inr Hlim => lbcompl Hlim c
    end.

  Lemma conv_bcompl {n} (c : bchain A n) m Hm : bcompl n c ≡{m}≡ c m Hm.
  Proof.
    rewrite /bcompl. destruct (SIdx.case _) as [[->|[m' ->]]|?]; simpl.
    - by destruct (SIdx.nlt_0_r m).
    - by apply bchain_cauchy, SIdx.lt_succ_r.
    - apply conv_lbcompl.
  Qed.

  Lemma bcompl_ne {n} (c1 c2 : bchain A n) m :
    (∀ p (Hp : p < n), c1 p Hp ≡{m}≡ c2 p Hp) →
    bcompl n c1 ≡{m}≡ bcompl n c2.
  Proof.
    intros Hc. rewrite /bcompl. destruct (SIdx.case _) as [[?|[m' ->]]|?]; simpl.
    - done.
    - apply Hc.
    - by apply lbcompl_ne.
  Qed.

  Lemma limit_preserving_bcompl (P : A → Prop) n (c : bchain A n) :
    n ≠ 0ᵢ ∨ P inhabitant →
    LimitPreserving P →
    (∀ m Hm, P (c m Hm)) → P (bcompl n c).
  Proof.
    intros H0 [Hcompl Hlbcompl] HP. rewrite /bcompl.
    destruct (SIdx.case _) as [[?|[m' ->]]|?]; naive_solver.
  Qed.
End bcompl.

(** We define the fixpoint of a contractive function [f : A → A] for an arbitrary
step-index type [SI]. To explain the fixpoint construction in the general case,
let us first recall the construction in the finite case. To find the fixpoint of
a contractive function [f], we start with some dummy element [x_0] (an arbitrary
inhabitant of [A]) and iterate [f] on it such that [x_1 := f x_0], [x_2 := f x_1],
... (i.e., [x_(n + 1) := f x_n]). We then find the fixpoint as the completion
[compl] of all of these fixpoint approximations (i.e., [x := compl (λ i, x_i)]).

In the general case with ordinals as step-indices, iterating over all natural
numbers is not enough. The way that this is solved is that COFEs provide
completion operations [lbcompl] for all limit ordinals as an additional
component of their definition. Then, conceptually, we can first define our
approximations as before for all natural numbers (i.e., [x_0, x_1, ...]) and
then we can define [x_ω := lbcompl ω (λ n, x_n)] to get the limit of all those
natural number approximations. Once we have [x_ω], we can start our iteration
again (i.e., [x_(ω + 1) := f (x_ω), ...]). We keep repeating this with all
ordinals until we have eventually defined [x_n] for all ordinals [n]. At that
point, we get a fixpoint by using the completion [x := compl (λ n, x_n)]
analogously to the natural number case.

There is one small caveat to this construction. In the definition of the
fixpoint, it is somewhat inconvenient to distinguish between the cases 0,
[Sᵢ n], and limit ordinals explicitly. We can get a very clean definition of the
fixpoint with a trick: we generalize the operation [lbcompl] that only works on
limit ordinals to work on arbitrary ordinals. This is the operation [bcompl]
defined above. *)

Section fixpoint.
  Context {SI : sidx} `{!Cofe A, !Inhabited A} (f : A → A) `{!Contractive f}.

  (** Getting Rocq to agree with the above description of the construction of the
  fixpoint takes a little work. To apply the completion operations (i.e.,
  [compl] and [bcompl]), we need to know that the fixed point approximations
  (i.e., ([x_n] for any [n]) and ([x_m] for any [n < m])) form a "chain".
  This is not an issue in the case of natural numbers, where we can
  simply proceed in three steps:
  1. We first define all [x_n] by recursion on [n].
  2. We prove that they form a chain, and
  3. We define [x := compl (λ n, x_n)] knowing that [(λ n, x_n)] is a chain.

  In the general case of ordinals, our life is harder. We want to use recursion
  on ordinals to define [x_n] in terms of its predecessors [x_m] for [m < n].
  However, to define [x_n], we need to use the bounded completion operation
  [bcompl], which can only be applied to "bounded chains". Thus, while defining
  [x_n], we need to know that all the previously defined [x_m] form a chain. In
  other words, we need a property about the sequence of elements that we have
  just defined. To that end, we define [bfchain], which packages a bounded chain
  [bfchain_car] with the property that applying [bcompl] to [bfchain_car] gives
  the fixpoint up to index [n]. *)

  (** Note that [bfchain] is a private implementation detail, but Rocq does not
  allow us to make records [Local]. *)
  Record bfchain n := {
    bfchain_car :> bchain A n;
    bfchain_fixpoint p :
      p < n → f (bcompl n bfchain_car) ≡{p}≡ bcompl n bfchain_car;
  }.

  Local Lemma bfchain_chain_unique {n m} (c1 : bfchain n) (c2 : bfchain m) p :
    p < n → p < m → bcompl n c1 ≡{p}≡ bcompl m c2.
  Proof using Type*.
    intros Hn Hm. induction (SIdx.lt_wf p) as [p _ IH].
    rewrite -(bfchain_fixpoint _ c2) // -(bfchain_fixpoint _ c1) //.
    apply (contractive_dist_later_dist _); split=> p' Hp'.
    apply IH; [done|by etrans..].
  Qed.

  Local Program Definition fixpoint_bchain_go n
      (rec : ∀ m, m < n → bfchain m) : bfchain n :=
    {| bfchain_car := {| bchain_car m' Hm' := f (bcompl m' (rec _ Hm')) |} |}.
  Next Obligation.
    intros n rec m m' Hmn Hmn' Hm; simpl.
    apply (contractive_dist_later_dist _); split=> p Hp.
    apply bfchain_chain_unique; eauto using SIdx.lt_le_trans.
  Qed.
  Next Obligation.
    intros n rec p Hp; simpl. rewrite (conv_bcompl _ _ Hp) /=.
    apply (contractive_dist_later_dist _); split=> p' Hp'. by apply rec.
  Qed.

  (** We obtain a bounded fixpoint chain for every index [n] by index recursion.
  In the recursive case, we construct a new chain up to [n] by taking,
  for any [m < n], the limit of the [m]-th chain before applying [f] to it. *)
  Local Definition fixpoint_bchain n : bfchain n :=
    Fix SIdx.lt_wf bfchain fixpoint_bchain_go n.

  (** We obtain a final full chain by repeating this construction for every [n],
     using the bounded chains computed before. *)
  Local Program Definition fixpoint_chain : chain A :=
    {| chain_car n := f (bcompl n (fixpoint_bchain n)) |}.
  Next Obligation.
    intros n m [Hnm| ->]%SIdx.le_lteq; simpl; [|done].
    apply (contractive_dist_later_dist _); split=> p Hp.
    apply bfchain_chain_unique; [by etrans|done].
  Qed.

  Local Definition fixpoint_def : A := compl fixpoint_chain.
  Local Definition fixpoint_aux : seal (@fixpoint_def).
  Proof using Type. by eexists. Qed.
  Definition fixpoint := fixpoint_aux.(unseal).
  Local Definition fixpoint_unseal :
    @fixpoint = @fixpoint_def := fixpoint_aux.(seal_eq).

  (** This lemma does not work well with [rewrite]; we usually define a specific
  unfolding lemma for each fixpoint and then [apply fixpoint_unfold] in the
  proof of that unfolding lemma. *)
  Lemma fixpoint_unfold : fixpoint ≡ f fixpoint.
  Proof.
    apply equiv_dist=> n. rewrite fixpoint_unseal /fixpoint_def /=.
    rewrite !conv_compl /fixpoint_chain /=.
    apply (contractive_dist_later_dist _); split=> p Hp.
    by rewrite bfchain_fixpoint.
  Qed.
End fixpoint.

Section fixpoint.
  Context {SI : sidx} `{!Cofe A, !Inhabited A} (f : A → A) `{!Contractive f}.

  Lemma fixpoint_unique (x : A) : x ≡ f x → x ≡ fixpoint f.
  Proof.
    rewrite !equiv_dist=> Hx n. induction (SIdx.lt_wf n) as [n _ IH].
    rewrite Hx fixpoint_unfold. f_contractive; eauto.
  Qed.

  Lemma fixpoint_ne (g : A → A) `{!Contractive g} n :
    (∀ z, f z ≡{n}≡ g z) → fixpoint f ≡{n}≡ fixpoint g.
  Proof.
    intros Hfg. induction (SIdx.lt_wf n) as [n _ IH].
    rewrite (fixpoint_unfold f) (fixpoint_unfold g) -Hfg.
    f_contractive. apply IH; eauto using dist_lt.
  Qed.
  Lemma fixpoint_proper (g : A → A) `{!Contractive g} :
    (∀ x, f x ≡ g x) → fixpoint f ≡ fixpoint g.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_ne. Qed.

  Lemma fixpoint_ind (P : A → Prop) :
    Proper ((≡) ==> impl) P →
    (∃ x, P x) →
    (∀ x, P x → P (f x)) →
    LimitPreserving P →
    P (fixpoint f).
  Proof.
    intros HP [x Hx] Hf Hlim. eapply HP.
    { eapply fixpoint_unique, (@fixpoint_unfold _ _ _ (populate x) f). }
    rewrite fixpoint_unseal /fixpoint_def. apply Hlim=> m /=.
    apply Hf. rewrite /fixpoint_bchain /Fix.
    generalize (SIdx.lt_wf m). revert m. fix IH 2=> m acc.
    apply limit_preserving_bcompl; [auto..|].
    intros m' Hm'. destruct acc as [acc]; simpl. apply Hf, IH.
  Qed.
End fixpoint.

(** Fixpoint of [f] when [f^k] is contractive. **)
Definition fixpointK {SI : sidx} `{!Cofe A, !Inhabited A} k (f : A → A)
  `{!Contractive (Nat.iter k f)} := fixpoint (Nat.iter k f).

Section fixpointK.
  Local Set Default Proof Using "Type*".
  Context {SI : sidx} {A : ofe} `{!Cofe A, !Inhabited A} (f : A → A) (k : nat).
  Context {f_contractive : Contractive (Nat.iter k f)} {f_ne : NonExpansive f}.

  (* Note than f_ne is crucial here:  there are functions f such that f^2 is contractive,
     but f is not non-expansive.
     Consider for example f: SPred → SPred (where SPred is "downclosed sets of natural numbers").
     Define f (using informative excluded middle) as follows:
     f(N) = N  (where N is the set of all natural numbers)
     f({0, ..., n}) = {0, ... n-1}  if n is even (so n-1 is at least -1, in which case we return the empty set)
     f({0, ..., n}) = {0, ..., n+2} if n is odd
     In other words, if we consider elements of SPred as ordinals, then we decreaste odd finite
     ordinals by 1 and increase even finite ordinals by 2.
     f is not non-expansive:  Consider f({0}) = ∅ and f({0,1}) = f({0,1,2,3}).
     The arguments are clearly 0-equal, but the results are not.

     Now consider g := f^2. We have
     g(N) = N
     g({0, ..., n}) = {0, ... n+1}  if n is even
     g({0, ..., n}) = {0, ..., n+4} if n is odd
     g is contractive.  All outputs contain 0, so they are all 0-equal.
     Now consider two n-equal inputs. We have to show that the outputs are n+1-equal.
     Either they both do not contain n in which case they have to be fully equal and
     hence so are the results.  Or else they both contain n, so the results will
     both contain n+1, so the results are n+1-equal.
   *)

  Let f_proper : Proper ((≡) ==> (≡)) f := ne_proper f.
  Local Existing Instance f_proper.

  Lemma fixpointK_unfold : fixpointK k f ≡ f (fixpointK k f).
  Proof.
    symmetry. rewrite /fixpointK. apply fixpoint_unique.
    by rewrite -Nat.iter_succ_r Nat.iter_succ -fixpoint_unfold.
  Qed.

  Lemma fixpointK_unique (x : A) : x ≡ f x → x ≡ fixpointK k f.
  Proof.
    intros Hf. apply fixpoint_unique. clear f_contractive.
    induction k as [|k' IH]=> //=. by rewrite -IH.
  Qed.

  Section fixpointK_ne.
    Context (g : A → A) `{g_contractive : !Contractive (Nat.iter k g)}.
    Context {g_ne : NonExpansive g}.

    Lemma fixpointK_ne n : (∀ z, f z ≡{n}≡ g z) → fixpointK k f ≡{n}≡ fixpointK k g.
    Proof.
      rewrite /fixpointK=> Hfg /=. apply fixpoint_ne=> z.
      clear f_contractive g_contractive.
      induction k as [|k' IH]=> //=. by rewrite IH Hfg.
    Qed.

    Lemma fixpointK_proper : (∀ z, f z ≡ g z) → fixpointK k f ≡ fixpointK k g.
    Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpointK_ne. Qed.
  End fixpointK_ne.

  Lemma fixpointK_ind (P : A → Prop) :
    Proper ((≡) ==> impl) P →
    (∃ x, P x) → (∀ x, P x → P (f x)) →
    LimitPreserving P →
    P (fixpointK k f).
  Proof.
    intros. rewrite /fixpointK. apply fixpoint_ind; eauto.
    intros; apply Nat.iter_ind; auto.
  Qed.
End fixpointK.

(** Mutual fixpoints *)
Section fixpointAB.
  Context {SI : sidx} {A B : ofe} `{!Cofe A, !Cofe B, !Inhabited A, !Inhabited B}.
  Context (fA : A → B → A).
  Context (fB : A → B → B).
  Context {fA_contractive : ∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context {fB_contractive : ∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.

  Local Definition fixpoint_AB (x : A) : B := fixpoint (fB x).
  Local Instance fixpoint_AB_contractive : Contractive fixpoint_AB.
  Proof.
    intros n x x' Hx; rewrite /fixpoint_AB.
    apply fixpoint_ne=> y. by f_contractive.
  Qed.

  Local Definition fixpoint_AA (x : A) : A := fA x (fixpoint_AB x).
  Local Instance fixpoint_AA_contractive : Contractive fixpoint_AA.
  Proof using fA_contractive. solve_contractive. Qed.

  Definition fixpoint_A : A := fixpoint fixpoint_AA.
  Definition fixpoint_B : B := fixpoint_AB fixpoint_A.

  Lemma fixpoint_A_unfold : fA fixpoint_A fixpoint_B ≡ fixpoint_A.
  Proof. by rewrite {2}/fixpoint_A (fixpoint_unfold _). Qed.
  Lemma fixpoint_B_unfold : fB fixpoint_A fixpoint_B ≡ fixpoint_B.
  Proof. by rewrite {2}/fixpoint_B /fixpoint_AB (fixpoint_unfold _). Qed.

  Local Instance: Proper ((≡) ==> (≡) ==> (≡)) fA.
  Proof using fA_contractive.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; eauto using dist_lt.
  Qed.
  Local Instance: Proper ((≡) ==> (≡) ==> (≡)) fB.
  Proof using fB_contractive.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; eauto using dist_lt.
  Qed.

  Lemma fixpoint_A_unique p q : fA p q ≡ p → fB p q ≡ q → p ≡ fixpoint_A.
  Proof.
    intros HfA HfB. rewrite -HfA. apply fixpoint_unique. rewrite /fixpoint_AA.
    f_equiv=> //. apply fixpoint_unique. by rewrite HfA HfB.
  Qed.
  Lemma fixpoint_B_unique p q : fA p q ≡ p → fB p q ≡ q → q ≡ fixpoint_B.
  Proof. intros. apply fixpoint_unique. by rewrite -fixpoint_A_unique. Qed.
End fixpointAB.

Section fixpointAB_ne.
  Context {SI : sidx} {A B : ofe} `{!Cofe A, !Cofe B, !Inhabited A, !Inhabited B}.
  Context (fA fA' : A → B → A).
  Context (fB fB' : A → B → B).
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA'}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB'}.

  Lemma fixpoint_A_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_A fA fB ≡{n}≡ fixpoint_A fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z.
    rewrite /fixpoint_AA /fixpoint_AB HfA. f_equiv. by apply fixpoint_ne.
  Qed.
  Lemma fixpoint_B_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_B fA fB ≡{n}≡ fixpoint_B fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z. rewrite HfB. f_contractive.
    apply fixpoint_A_ne; eauto using dist_lt.
  Qed.

  Lemma fixpoint_A_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_A fA fB ≡ fixpoint_A fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_A_ne. Qed.
  Lemma fixpoint_B_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_B fA fB ≡ fixpoint_B fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_B_ne. Qed.
End fixpointAB_ne.

(** Non-expansive function space *)
Record ofe_mor {SI : sidx} (A B : ofe) : Type := OfeMor {
  ofe_mor_car :> A → B;
  ofe_mor_ne : NonExpansive ofe_mor_car
}.
Global Arguments OfeMor {_ _ _} _ {_}.
Add Printing Constructor ofe_mor.
Global Existing Instance ofe_mor_ne.

Notation "'λne' x .. y , t" :=
  (@OfeMor _ _ _ (λ x, .. (@OfeMor _ _ _ (λ y, t) _) ..) _)
  (at level 200, x binder, y binder, right associativity).

Section ofe_mor.
  Context {SI : sidx} {A B : ofe}.

  Global Instance ofe_mor_proper (f : ofe_mor A B) : Proper ((≡) ==> (≡)) f.
  Proof. apply ne_proper, ofe_mor_ne. Qed.

  Local Instance ofe_mor_equiv : Equiv (ofe_mor A B) := λ f g, ∀ x, f x ≡ g x.
  Local Instance ofe_mor_dist : Dist (ofe_mor A B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition ofe_mor_ofe_mixin : OfeMixin (ofe_mor A B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - intros n m f g ? x ?; eauto using dist_le.
  Qed.
  Canonical Structure ofe_morO := Ofe (ofe_mor A B) ofe_mor_ofe_mixin.

  Program Definition ofe_mor_chain (c : chain ofe_morO)
    (x : A) : chain B := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Program Definition ofe_mor_compl `{!Cofe B} : Compl ofe_morO := λ c,
    {| ofe_mor_car x := compl (ofe_mor_chain c x) |}.
  Next Obligation.
    intros ? c n x y Hx. by rewrite (conv_compl n (ofe_mor_chain c x))
      (conv_compl n (ofe_mor_chain c y)) /= Hx.
  Qed.

  Program Definition ofe_mor_bchain {n}
      (c : bchain ofe_morO n) (x : A) : bchain B n :=
    {| bchain_car n Hn := c n Hn x |}.
  Next Obligation. intros n c x m Hm i ??. by apply (bchain_cauchy n c). Qed.
  Program Definition ofe_mor_lbcompl `{!Cofe B} : LBCompl ofe_morO := λ n Hn c,
    {| ofe_mor_car x := lbcompl Hn (ofe_mor_bchain c x) |}.
  Next Obligation.
    intros ? n Hn c m x y Hx. apply lbcompl_ne=> p ?.
    rewrite /ofe_mor_bchain /=. by rewrite Hx.
  Qed.

  Global Program Instance ofe_mor_cofe `{!Cofe B} : Cofe ofe_morO :=
    {| compl := ofe_mor_compl; lbcompl := ofe_mor_lbcompl |}.
  Next Obligation. intros ? n c x; simpl. by rewrite conv_compl. Qed.
  Next Obligation.
    intros ? n Hn m Hm H x; simpl. rewrite (conv_lbcompl Hn) //=.
  Qed.
  Next Obligation.
    intros ? n Hn c1 c2 m Hc x; simpl. apply lbcompl_ne=> p Hp. apply Hc.
  Qed.

  Global Instance ofe_mor_car_ne : NonExpansive2 (@ofe_mor_car SI A B).
  Proof. intros n f g Hfg x y Hx; rewrite Hx; apply Hfg. Qed.
  Global Instance ofe_mor_car_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@ofe_mor_car SI A B) := ne_proper_2 _.
  Lemma ofe_mor_ext (f g : ofe_mor A B) : f ≡ g ↔ ∀ x, f x ≡ g x.
  Proof. done. Qed.
End ofe_mor.

Global Arguments ofe_morO {_} _ _.
Notation "A -n> B" :=
  (ofe_morO A B) (at level 99, B at level 200, right associativity).
Global Instance ofe_mor_inhabited {SI : sidx} {A B : ofe} `{Inhabited B} :
  Inhabited (A -n> B) := populate (λne _, inhabitant).

(** Identity and composition and constant function *)
Definition cid {SI : sidx} {A: ofe} : A -n> A := OfeMor id.
Global Instance: Params (@cid) 2 := {}.
Definition cconst {SI : sidx} {A B : ofe} (x : B) : A -n> B := OfeMor (const x).
Global Instance: Params (@cconst) 3 := {}.

Definition ccompose {SI : sidx} {A B C: ofe}
  (f : B -n> C) (g : A -n> B) : A -n> C := OfeMor (f ∘ g).
Global Instance: Params (@ccompose) 4 := {}.
Infix "◎" := ccompose (at level 40, left associativity).
Global Instance ccompose_ne {SI : sidx} {A B C: ofe} :
  NonExpansive2 (@ccompose SI A B C).
Proof. intros n ?? Hf g1 g2 Hg x. rewrite /= (Hg x) (Hf (g2 x)) //. Qed.
Global Instance ccompose_proper {SI : sidx} {A B C: ofe} :
  Proper ((≡) ==> (≡) ==> (≡)) (@ccompose SI A B C).
Proof. apply ne_proper_2; apply _. Qed.

(* Function space maps *)
Definition ofe_mor_map {SI : sidx} {A A' B B': ofe}
    (f : A' -n> A) (g : B -n> B') (h : A -n> B) : A' -n> B' :=
  g ◎ h ◎ f.
Global Instance ofe_mor_map_ne {SI : sidx} {A A' B B': ofe} :
  NonExpansive3 (@ofe_mor_map SI A A' B B').
Proof. intros n ??? ??? ???. by repeat apply ccompose_ne. Qed.

Definition ofe_morO_map {SI : sidx} {A A' B B': ofe}
    (f : A' -n> A) (g : B -n> B') : (A -n> B) -n> (A' -n>  B') :=
  OfeMor (ofe_mor_map f g).
Global Instance ofe_morO_map_ne {SI : sidx} {A A' B B': ofe} :
  NonExpansive2 (@ofe_morO_map SI A A' B B').
Proof.
  intros n f f' Hf g g' Hg ?. rewrite /= /ofe_mor_map.
  by repeat apply ccompose_ne.
Qed.

(** * Unit type *)
Section unit.
  Context {SI : sidx}.

  Local Instance unit_dist : Dist unit := λ _ _ _, True.
  Definition unit_ofe_mixin : OfeMixin unit.
  Proof. repeat split. Qed.
  Canonical Structure unitO : ofe := Ofe unit unit_ofe_mixin.

  Global Program Instance unit_cofe : Cofe unitO :=
    { compl x := (); lbcompl _ _ _ := () }.
  Solve All Obligations with by repeat split.

  Global Instance unit_ofe_discrete : OfeDiscrete unitO.
  Proof. done. Qed.
End unit.

(** * Empty type *)
Section empty.
  Context {SI : sidx}.

  Local Instance Empty_set_dist : Dist Empty_set := λ _ _ _, True.
  Definition Empty_set_ofe_mixin : OfeMixin Empty_set.
  Proof. by repeat split. Qed.
  Canonical Structure Empty_setO : ofe := Ofe Empty_set Empty_set_ofe_mixin.

  Global Program Instance Empty_set_cofe : Cofe Empty_setO :=
    {| compl c := c 0ᵢ; lbcompl n Hn c := c _ (SIdx.limit_lt_0 _ Hn) |}.
  Solve All Obligations with done.

  Global Instance Empty_set_ofe_discrete : OfeDiscrete Empty_setO.
  Proof. done. Qed.
End empty.

(** * Product type *)
Section product.
  Context {SI : sidx} {A B : ofe}.

  Local Instance prod_dist : Dist (A * B) := λ n, prod_relation (dist n) (dist n).
  Global Instance pair_ne :
    NonExpansive2 (@pair A B) := _.
  Global Instance fst_ne : NonExpansive (@fst A B) := _.
  Global Instance snd_ne : NonExpansive (@snd A B) := _.

  Definition prod_ofe_mixin : OfeMixin (A * B).
  Proof.
    split.
    - intros x y; unfold dist, prod_dist, equiv, prod_equiv, prod_relation.
      rewrite !equiv_dist; naive_solver.
    - apply _.
    - by intros n m [x1 y1] [x2 y2] [??]; split; eapply dist_le.
  Qed.
  Canonical Structure prodO : ofe := Ofe (A * B) prod_ofe_mixin.

  Global Program Instance prod_cofe `{!Cofe A, !Cofe B} : Cofe prodO := {
    compl c := (compl (chain_map fst c), compl (chain_map snd c));
    lbcompl n Hn c := (lbcompl Hn (bchain_map fst c), lbcompl Hn (bchain_map snd c))
  }.
  Next Obligation. split; simpl; rewrite conv_compl //. Qed.
  Next Obligation. split; simpl; rewrite conv_lbcompl //=. Qed.
  Next Obligation. split; simpl; apply lbcompl_ne=> ?? /=; f_equiv; auto. Qed.

  Global Instance prod_discrete (x : A * B) :
    Discrete (x.1) → Discrete (x.2) → Discrete x.
  Proof. by intros ???[??]; split; apply (discrete_0 _). Qed.
  Global Instance prod_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete prodO.
  Proof. intros ?? [??]; apply _. Qed.

  Lemma pair_dist n (a1 a2 : A) (b1 b2 : B) :
    (a1, b1) ≡{n}≡ (a2, b2) ↔ a1 ≡{n}≡ a2 ∧ b1 ≡{n}≡ b2.
  Proof. reflexivity. Qed.
End product.

Global Arguments prodO {_} _ _.

(** Below we make [prod_dist] type class opaque, so we first lift all
instances *)
Global Instance pair_dist_inj {SI : sidx} {A B : ofe} n :
  Inj2 (≡{n}≡) (≡{n}≡) (≡{n}≡) (@pair A B) := _.

Global Instance curry_ne {SI : sidx} {A B C : ofe} n :
  Proper (((≡{n}@{A*B}≡) ==> (≡{n}@{C}≡)) ==>
          (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) curry := _.
Global Instance uncurry_ne {SI : sidx} {A B C : ofe} n :
  Proper (((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) ==>
          (≡{n}@{A*B}≡) ==> (≡{n}@{C}≡)) uncurry := _.

Global Instance curry3_ne {SI : sidx} {A B C D : ofe} n :
  Proper (((≡{n}@{A*B*C}≡) ==> (≡{n}@{D}≡)) ==>
          (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) curry3 := _.
Global Instance uncurry3_ne {SI : sidx} {A B C D : ofe} n :
  Proper (((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) ==>
          (≡{n}@{A*B*C}≡) ==> (≡{n}@{D}≡)) uncurry3 := _.

Global Instance curry4_ne {SI : sidx} {A B C D E : ofe} n :
  Proper (((≡{n}@{A*B*C*D}≡) ==> (≡{n}@{E}≡)) ==>
          (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) curry4 := _.
Global Instance uncurry4_ne {SI : sidx} {A B C D E : ofe} n :
  Proper (((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) ==>
          (≡{n}@{A*B*C*D}≡) ==> (≡{n}@{E}≡)) uncurry4 := _.

Global Typeclasses Opaque prod_dist.

Global Instance prod_map_ne {SI : sidx} {A A' B B' : ofe} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@prod_map A A' B B').
Proof. by intros f f' Hf g g' Hg ?? [??]; split; [apply Hf|apply Hg]. Qed.
Definition prodO_map {SI : sidx} {A A' B B'} (f : A -n> A') (g : B -n> B') :
  prodO A B -n> prodO A' B' := OfeMor (prod_map f g).
Global Instance prodO_map_ne {SI : sidx} {A A' B B'} :
  NonExpansive2 (@prodO_map SI A A' B B').
Proof. intros n f f' Hf g g' Hg [??]; split; [apply Hf|apply Hg]. Qed.

(** * COFE → OFE Functors *)
Record oFunctor {SI : sidx} := OFunctor {
  oFunctor_car : ∀ A `{!Cofe A} B `{!Cofe B}, ofe;
  oFunctor_map `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → oFunctor_car A1 B1 -n> oFunctor_car A2 B2;
  oFunctor_map_ne `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    NonExpansive (@oFunctor_map A1 _ A2 _ B1 _ B2 _);
  oFunctor_map_id `{!Cofe A, !Cofe B} (x : oFunctor_car A B) :
    oFunctor_map (cid,cid) x ≡ x;
  oFunctor_map_compose `{!Cofe A1, !Cofe A2, !Cofe A3, !Cofe B1, !Cofe B2, !Cofe B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    oFunctor_map (f◎g, g'◎f') x ≡ oFunctor_map (g,g') (oFunctor_map (f,f') x)
}.
Global Existing Instance oFunctor_map_ne.
Global Instance: Params (@oFunctor_map) 10 := {}.

Declare Scope oFunctor_scope.
Delimit Scope oFunctor_scope with OF.
Bind Scope oFunctor_scope with oFunctor.

Class oFunctorContractive {SI : sidx} (F : oFunctor) :=
  #[global] oFunctor_map_contractive `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} ::
    Contractive (@oFunctor_map SI F A1 _ A2 _ B1 _ B2 _).
Global Hint Mode oFunctorContractive - ! : typeclass_instances.

(** Not a coercion due to the [Cofe] type class argument, and to avoid
ambiguous coercion paths, see https://gitlab.mpi-sws.org/iris/iris/issues/240. *)
Definition oFunctor_apply {SI : sidx} (F : oFunctor) (A : ofe) `{!Cofe A} : ofe :=
  oFunctor_car F A A.

Program Definition oFunctor_oFunctor_compose {SI : sidx} (F1 F2 : oFunctor)
  `{!∀ `{!Cofe A, !Cofe B}, Cofe (oFunctor_car F2 A B)} : oFunctor := {|
  oFunctor_car A _ B _ := oFunctor_car F1 (oFunctor_car F2 B A) (oFunctor_car F2 A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ 'fg :=
    oFunctor_map F1 (oFunctor_map F2 (fg.2,fg.1),oFunctor_map F2 fg)
|}.
Next Obligation.
  intros SI F1 F2 ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] [??]; simpl in *.
  apply oFunctor_map_ne; split; apply oFunctor_map_ne; by split.
Qed.
Next Obligation.
  intros SI F1 F2 ? A ? B ? x; simpl in *. rewrite -{2}(oFunctor_map_id F1 x).
  apply equiv_dist=> n. apply oFunctor_map_ne.
  split=> y /=; by rewrite !oFunctor_map_id.
Qed.
Next Obligation.
  intros SI F1 F2 ? A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -oFunctor_map_compose. apply equiv_dist=> n. apply oFunctor_map_ne.
  split=> y /=; by rewrite !oFunctor_map_compose.
Qed.
Global Instance oFunctor_oFunctor_compose_contractive_1 {SI : sidx} (F1 F2 : oFunctor)
    `{!∀ `{!Cofe A, !Cofe B}, Cofe (oFunctor_car F2 A B)} :
  oFunctorContractive F1 → oFunctorContractive (oFunctor_oFunctor_compose F1 F2).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_contractive; destruct Hfg; split; simpl in *; apply oFunctor_map_ne; by split.
Qed.
Global Instance oFunctor_oFunctor_compose_contractive_2 {SI : sidx} (F1 F2 : oFunctor)
    `{!∀ `{!Cofe A, !Cofe B}, Cofe (oFunctor_car F2 A B)} :
  oFunctorContractive F2 → oFunctorContractive (oFunctor_oFunctor_compose F1 F2).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_equiv; split; simpl in *; f_contractive; destruct Hfg; by split.
Qed.

Program Definition constOF {SI : sidx} (B : ofe) : oFunctor :=
  {| oFunctor_car A1 A2 _ _ := B; oFunctor_map A1 _ A2 _ B1 _ B2 _ f := cid |}.
Solve Obligations with done.
Coercion constOF : ofe >-> oFunctor.

Global Instance constOF_contractive {SI : sidx} B : oFunctorContractive (constOF B).
Proof. rewrite /oFunctorContractive; apply _. Qed.

Program Definition idOF {SI : sidx} : oFunctor :=
  {| oFunctor_car A1 _ A2 _ := A2; oFunctor_map A1 _ A2 _ B1 _ B2 _ f := f.2 |}.
Solve Obligations with done.
Notation "∙" := idOF : oFunctor_scope.

Program Definition prodOF {SI : sidx} (F1 F2 : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := prodO (oFunctor_car F1 A B) (oFunctor_car F2 A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    prodO_map (oFunctor_map F1 fg) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros ??? A1 ? A2 ? B1 ? B2 ? n ???; by apply prodO_map_ne; apply oFunctor_map_ne.
Qed.
Next Obligation. by intros ? F1 F2 A ? B ? [??]; rewrite /= !oFunctor_map_id. Qed.
Next Obligation.
  intros ? F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [??]; simpl.
  by rewrite !oFunctor_map_compose.
Qed.
Notation "F1 * F2" := (prodOF F1%OF F2%OF) : oFunctor_scope.

Global Instance prodOF_contractive {SI : sidx} F1 F2 :
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (prodOF F1 F2).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n ???;
    by apply prodO_map_ne; apply oFunctor_map_contractive.
Qed.

Program Definition ofe_morOF {SI : sidx} (F1 F2 : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := oFunctor_car F1 B A -n> oFunctor_car F2 A B;
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    ofe_morO_map (oFunctor_map F1 (fg.2, fg.1)) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros ? F1 F2 A1 ? A2 ? B1 ? B2 ? n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morO_map_ne; apply oFunctor_map_ne; split; by apply Hfg.
Qed.
Next Obligation.
  intros ? F1 F2 A ? B ? [f ?] ?; simpl. rewrite /= !oFunctor_map_id.
  apply (ne_proper f). apply oFunctor_map_id.
Qed.
Next Obligation.
  intros ? F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [h ?] ?; simpl in *.
  rewrite -!oFunctor_map_compose. do 2 apply (ne_proper _). apply oFunctor_map_compose.
Qed.
Notation "F1 -n> F2" := (ofe_morOF F1%OF F2%OF) : oFunctor_scope.

Global Instance ofe_morOF_contractive {SI : sidx} F1 F2 :
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (ofe_morOF F1 F2).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morO_map_ne; apply oFunctor_map_contractive;
    split; intros m Hlt; split; simpl.
  all: destruct Hfg as [Hfg]; destruct (Hfg m); auto.
Qed.

(** * Sum type *)
Section sum.
  Context {SI : sidx} {A B : ofe}.

  Local Instance sum_dist : Dist (A + B) := λ n, sum_relation (dist n) (dist n).
  Global Instance inl_ne : NonExpansive (@inl A B) := _.
  Global Instance inr_ne : NonExpansive (@inr A B) := _.
  Global Instance inl_ne_inj n : Inj (dist n) (dist n) (@inl A B) := _.
  Global Instance inr_ne_inj n : Inj (dist n) (dist n) (@inr A B) := _.

  Definition sum_ofe_mixin : OfeMixin (A + B).
  Proof.
    split.
    - intros x y; split=> Hx.
      + destruct Hx=> n; constructor; by apply equiv_dist.
      + destruct (Hx 0ᵢ); constructor; apply equiv_dist=> n; by apply (inj _).
    - apply _.
    - destruct 1; constructor; eapply dist_le; eauto.
  Qed.
  Canonical Structure sumO : ofe := Ofe (A + B) sum_ofe_mixin.

  (** The [compl] operator for sums is tricky. We are are given a [chain (A + B)]
  and need to turn it into a [chain A] or [chain B] to use the [compl] operation
  on [A] and [B], respectively. A priori it seems that a [chain (A + B)] might
  contain [inl] and [inr] elements in a mixed fashion, but this is not the case.
  Once we have inspected the first element [c 0ᵢ] and established it is an [inl]
  or [inr], we know the whole chain contains [inl] or [inr] elements.

  Encoding this knowledge using dependent types is annoying, hence the functions
  [inl_chain] and [inr_chain] take a default value [a] and [b] to handle the
  impossible [inr] and [inl] cases. The function [sum_compl] only calls
  [inl_chain] if the first element is [inl a], so it can easily supply such a
  default (and similar for [inr]). In the proofs of [sum_cofe] we show that
  these cases cannot occur. *)
  Program Definition inl_chain (c : chain sumO) (a : A) : chain A :=
    {| chain_car n := match c n return _ with inl a' => a' | _ => a end |}.
  Next Obligation. intros c a n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
  Program Definition inr_chain (c : chain sumO) (b : B) : chain B :=
    {| chain_car n := match c n return _ with inr b' => b' | _ => b end |}.
  Next Obligation. intros c b n i ?; simpl. by destruct (chain_cauchy c n i). Qed.

  Definition sum_compl `{!Cofe A, !Cofe B} : Compl sumO := λ c,
    match c 0ᵢ with
    | inl a => inl (compl (inl_chain c a))
    | inr b => inr (compl (inr_chain c b))
    end.

  (** The definition of [bcompl] follows the same pattern as [compl] with the
  caveat that we need to show that [0ᵢ] is below [n] (for which we use
  [SIdx.limit_lt_0]). *)
  Program Definition inl_bchain {n} (c : bchain sumO n) (a : A) : bchain A n :=
    {| bchain_car n Hn := match c n Hn return _ with inl a' => a' | _ => a end |}.
  Next Obligation.
    intros n c a m p Hm Hp Hmp; simpl.
    by destruct (bchain_cauchy n c m p Hm Hp Hmp).
  Qed.
  Program Definition inr_bchain {n} (c : bchain sumO n) (b : B) : bchain B n :=
    {| bchain_car n Hn := match c n Hn return _ with inr b' => b' | _ => b end |}.
  Next Obligation.
    intros n c b m p Hm Hp Hmp; simpl.
    by destruct (bchain_cauchy n c m p Hm Hp Hmp).
  Qed.

  Definition sum_lbcompl `{!Cofe A, !Cofe B} : LBCompl sumO := λ n Hn c,
    match c 0ᵢ (SIdx.limit_lt_0 _ Hn) with
    | inl a => inl (lbcompl Hn (inl_bchain c a))
    | inr b => inr (lbcompl Hn (inr_bchain c b))
    end.

  Global Program Instance sum_cofe `{!Cofe A, !Cofe B} : Cofe sumO :=
    { compl := sum_compl; lbcompl := sum_lbcompl }.
  Next Obligation.
    intros ?? n c; rewrite /compl /sum_compl.
    oinversion (chain_cauchy c 0ᵢ n); first apply SIdx.le_0_l.
    - rewrite (conv_compl n (inl_chain c _)) /=. destruct (c n); naive_solver.
    - rewrite (conv_compl n (inr_chain c _)) /=. destruct (c n); naive_solver.
  Qed.
  Next Obligation.
    intros ?? n Hn c m Hm; rewrite /sum_lbcompl.
    oinversion (bchain_cauchy n c 0ᵢ m (SIdx.limit_lt_0 _ Hn) Hm);
      first apply SIdx.le_0_l.
    - rewrite (conv_lbcompl Hn _ Hm) /=. destruct (c m _); naive_solver.
    - rewrite (conv_lbcompl Hn _ Hm) /=. destruct (c m _); naive_solver.
  Qed.
  Next Obligation.
    intros ?? n Hn c1 c2 m Hc. rewrite /sum_lbcompl.
    destruct (Hc 0ᵢ (SIdx.limit_lt_0 _ Hn));
      rewrite /= lbcompl_ne //=; intros p Hp; by destruct (Hc p Hp).
  Qed.

  Global Instance inl_discrete (x : A) : Discrete x → Discrete (inl x).
  Proof. inversion_clear 2; constructor; by apply (discrete_0 _). Qed.
  Global Instance inr_discrete (y : B) : Discrete y → Discrete (inr y).
  Proof. inversion_clear 2; constructor; by apply (discrete_0 _). Qed.
  Global Instance sum_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete sumO.
  Proof. intros ?? [?|?]; apply _. Qed.
End sum.

Global Arguments sumO {_} _ _.
Global Typeclasses Opaque sum_dist.

Global Instance sum_map_ne {SI : sidx} {A A' B B' : ofe} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@sum_map A A' B B').
Proof.
  intros f f' Hf g g' Hg ??; destruct 1; constructor; [by apply Hf|by apply Hg].
Qed.
Definition sumO_map {SI : sidx} {A A' B B'} (f : A -n> A') (g : B -n> B') :
  sumO A B -n> sumO A' B' := OfeMor (sum_map f g).
Global Instance sumO_map_ne {SI : sidx} {A A' B B'} :
  NonExpansive2 (@sumO_map SI A A' B B').
Proof. intros n f f' Hf g g' Hg [?|?]; constructor; [apply Hf|apply Hg]. Qed.

Program Definition sumOF {SI : sidx} (F1 F2 : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := sumO (oFunctor_car F1 A B) (oFunctor_car F2 A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    sumO_map (oFunctor_map F1 fg) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros ??? A1 ? A2 ? B1 ? B2 ? n ???;
    by apply sumO_map_ne; apply oFunctor_map_ne.
Qed.
Next Obligation.
  by intros ? F1 F2 A ? B ? [?|?]; rewrite /= !oFunctor_map_id.
Qed.
Next Obligation.
  intros ? F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [?|?]; simpl;
    by rewrite !oFunctor_map_compose.
Qed.
Notation "F1 + F2" := (sumOF F1%OF F2%OF) : oFunctor_scope.

Global Instance sumOF_contractive {SI : sidx} F1 F2 :
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (sumOF F1 F2).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n ???;
    by apply sumO_map_ne; apply oFunctor_map_contractive.
Qed.

(** * Discrete OFEs *)
Section discrete_ofe.
  Context {SI : sidx} `{Equiv A} (Heq : @Equivalence A (≡)).

  Local Instance discrete_dist : Dist A := λ n x y, x ≡ y.
  Definition discrete_ofe_mixin : OfeMixin A.
  Proof using Type*.
    split.
    - intros x y; split; [done|intros Hn; apply (Hn 0ᵢ)].
    - done.
    - done.
  Qed.

  Global Instance discrete_ofe_discrete : OfeDiscrete (Ofe A discrete_ofe_mixin).
  Proof. by intros x y. Qed.

  Global Program Instance discrete_cofe : Cofe (Ofe A discrete_ofe_mixin) :=
    { compl c := c 0ᵢ; lbcompl n Hn c := c _ (SIdx.limit_lt_0 _ Hn) }.
  Next Obligation.
    intros n c; simpl. symmetry. apply (chain_cauchy c 0ᵢ n), SIdx.le_0_l.
  Qed.
  Next Obligation.
    intros n Hn c m Hm; simpl.
    symmetry; apply (bchain_cauchy n c 0ᵢ m), SIdx.le_0_l.
  Qed.
  Next Obligation. simpl; eauto. Qed.
End discrete_ofe.

(** The combinators [discreteO] and [leibnizO] should be used with care. There
are two ways in which they can be used:

1. To define an OFE on a ground type, such as [nat], [expr], etc. The OFE
   instance should be defined as [Canonical Structure tyO := leibnizO ty] or
   [Canonical Structure tyO := discreteO ty], so not using [Definition]. See
   [natO] below for an example. Make sure to avoid overlapping instances, so
   always check if no instance has already been defined. For most of the types
   from Rocq, std++, and Iris, instances are present in Iris. The convention is
   to use the name [tyO] for the OFE instance of a type [ty].
2. As part of abstractions that are parametrized with a [Type], but where an
   [ofe] is needed to use (camera) combinators. See [ghost_var] as an example.
   In this case, the public API of the abstraction should exclusively use
   [Type], i.e., the use of [leibnizO] or [discreteO] should not leak. Otherwise
   client code can end up with overlapping instances, and thus experience odd
   unification failures.

You should *never* use [leibnizO] or [discreteO] on compound types such as
[list nat]. That creates overlapping canonical instances for the head symbol
(e.g., [listO] and [leibnizO (list nat)]) and confuses unification. Instead, you
have two options:
- declare/use a canonical instance for the ground type, e.g., [listO natO].
- declare a newtype, e.g., [Record ty := Ty { ty_car : list nat }], and then
  declare a canonical instance for that type, e.g.,
  [Canonical Structure tyO := leibnizO ty]. *)

(** The combinator [discreteO A] lifts an existing [Equiv A] instance into a
discrete OFE. *)
Notation discreteO A := (Ofe A (discrete_ofe_mixin _)).

(** The combinator [leibnizO A] lifts Leibniz equality [=] into a discrete OFE.
The implementation forces the [Equivalence] proof to be [eq_equivalence] so that
Rocq does not accidentally use another one, like [ofe_equivalence], in the case of
aliases. See also https://gitlab.mpi-sws.org/iris/iris/issues/299 *)
Notation leibnizO A := (Ofe A (@discrete_ofe_mixin _ _ equivL eq_equivalence)).

(** In order to define a discrete CMRA with carrier [A] (in the file [cmra.v])
we need to determine the [Equivalence A] proof that was used to construct the
OFE instance of [A] (note that this proof is not the same as the one we obtain
via [ofe_equivalence]).

We obtain the proof of [Equivalence A] by inferring the canonical OFE mixin
using [ofe_mixin_of A], and then check whether it is indeed a discrete OFE. This
will fail if no OFE, or an OFE other than the discrete OFE, was registered. *)
Notation discrete_ofe_equivalence_of A := ltac:(
  match constr:(ofe_mixin_of A) with
  | discrete_ofe_mixin ?H => exact H
  end) (only parsing).

Global Instance leibnizO_leibniz {SI : sidx} A  : LeibnizEquiv (leibnizO A).
Proof. by intros x y. Qed.

(** * Basic Rocq types *)
Canonical Structure boolO {SI : sidx} : ofe := leibnizO bool.
Canonical Structure natO {SI : sidx} : ofe := leibnizO nat.
Canonical Structure positiveO {SI : sidx} : ofe := leibnizO positive.
Canonical Structure NO {SI : sidx} : ofe := leibnizO N.
Canonical Structure ZO {SI : sidx} : ofe := leibnizO Z.

Section prop.
  Context {SI : sidx}.

  Local Instance Prop_equiv : Equiv Prop := iff.
  Local Instance Prop_equivalence : Equivalence (≡@{Prop}) := _.
  Canonical Structure PropO := discreteO Prop.
End prop.

(** * Option type *)
Section option.
  Context {SI : sidx} {A : ofe}.

  Local Instance option_dist : Dist (option A) := λ n, option_Forall2 (dist n).
  Lemma option_dist_Forall2 n mx my : mx ≡{n}≡ my ↔ option_Forall2 (dist n) mx my.
  Proof. done. Qed.

  Definition option_ofe_mixin : OfeMixin (option A).
  Proof.
    split.
    - intros mx my; split; [by destruct 1; constructor; apply equiv_dist|].
      intros Hxy; destruct (Hxy 0ᵢ); constructor; apply equiv_dist.
      by intros n; oinversion (Hxy n).
    - apply _.
    - destruct 1; constructor; by eapply dist_le.
  Qed.
  Canonical Structure optionO := Ofe (option A) option_ofe_mixin.

  Global Instance Some_ne : NonExpansive (@Some A).
  Proof. intros ????. by econstructor. Qed.
  Global Instance Some_dist_inj n : Inj (dist n) (dist n) (@Some A).
  Proof. by inversion_clear 1. Qed.

  Program Definition option_chain (c : chain optionO) (x : A) : chain A :=
    {| chain_car n := default x (c n) |}.
  Next Obligation. intros c x n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
  Definition option_compl `{!Cofe A} : Compl optionO := λ c,
    match c 0ᵢ with Some x => Some (compl (option_chain c x)) | None => None end.

  Program Definition option_bchain n (c : bchain optionO n) (x : A) : bchain A n :=
    {| bchain_car n Hn := default x (c n Hn) |}.
  Next Obligation.
    intros n c x m p Hm Hp Hmp; simpl.
    by destruct (bchain_cauchy n c m p Hm Hp Hmp).
  Qed.
  Definition option_lbcompl `{!Cofe A} : LBCompl optionO := λ n Hn c,
    match c _ (SIdx.limit_lt_0 _ Hn) with
    | Some x => Some (lbcompl Hn (option_bchain n c x))
    | None => None
    end.

  Global Program Instance option_cofe `{!Cofe A} : Cofe optionO :=
    { compl := option_compl; lbcompl := option_lbcompl }.
  Next Obligation.
    intros ? n c. rewrite /compl /option_compl.
    oinversion (chain_cauchy c 0ᵢ n); [by apply SIdx.le_0_l|..]; f_equiv.
    rewrite (conv_compl n (option_chain c _)) /=. destruct (c n); naive_solver.
  Qed.
  Next Obligation.
    intros ? n Hn c m Hm. rewrite /lbcompl /option_lbcompl.
    oinversion (bchain_cauchy n c 0ᵢ m (SIdx.limit_lt_0 _ Hn) Hm);
      [by apply SIdx.le_0_l|..]; f_equiv.
    rewrite (conv_lbcompl _ _ Hm) /=. destruct (c m Hm); naive_solver.
  Qed.
  Next Obligation.
    intros ? n Hn c1 c2 m Hc. rewrite /lbcompl /option_lbcompl.
    destruct (Hc 0ᵢ (SIdx.limit_lt_0 _ Hn)); f_equiv.
    apply lbcompl_ne=> p Hp /=. by destruct (Hc p Hp).
  Qed.

  Global Instance option_ofe_discrete : OfeDiscrete A → OfeDiscrete optionO.
  Proof. destruct 2; constructor; by apply (discrete_0 _). Qed.

  Global Instance is_Some_ne n : Proper (dist n ==> iff) (@is_Some A).
  Proof. destruct 1; split; eauto. Qed.
  Global Instance from_option_ne {B} (R : relation B) n :
    Proper ((dist (A:=A) n ==> R) ==> R ==> dist n ==> R) from_option.
  Proof. destruct 3; simpl; auto. Qed.

  Global Instance None_discrete : Discrete (@None A).
  Proof. inversion_clear 1; constructor. Qed.
  Global Instance Some_discrete x : Discrete x → Discrete (Some x).
  Proof. by intros ?; inversion_clear 1; constructor; apply discrete_0. Qed.

  Lemma dist_None n mx : mx ≡{n}≡ None ↔ mx = None.
  Proof. split; [by inversion_clear 1|by intros ->]. Qed.
  Lemma dist_Some n x y : Some x ≡{n}≡ Some y ↔ x ≡{n}≡ y.
  Proof. split; [by inversion_clear 1 | by intros ->]. Qed.
  Lemma dist_Some_inv_l n mx my x :
    mx ≡{n}≡ my → mx = Some x → ∃ y, my = Some y ∧ x ≡{n}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_r n mx my y :
    mx ≡{n}≡ my → my = Some y → ∃ x, mx = Some x ∧ x ≡{n}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_l' n my x : Some x ≡{n}≡ my → ∃ x', Some x' = my ∧ x ≡{n}≡ x'.
  Proof. intros ?%(dist_Some_inv_l _ _ _ x); naive_solver. Qed.
  Lemma dist_Some_inv_r' n mx y : mx ≡{n}≡ Some y → ∃ y', mx = Some y' ∧ y ≡{n}≡ y'.
  Proof. intros ?%(dist_Some_inv_r _ _ _ y); naive_solver. Qed.
End option.

Global Typeclasses Opaque option_dist.
Global Arguments optionO {_} _.

Global Instance option_fmap_ne {SI : sidx} {A B : ofe} n :
  Proper ((dist n ==> dist n) ==> (≡{n}@{option A}≡) ==> (≡{n}@{option B}≡)) fmap.
Proof. intros f f' Hf ?? []; constructor; auto. Qed.
Global Instance option_mbind_ne {SI : sidx} {A B : ofe} n :
  Proper ((dist n ==> dist n) ==> (≡{n}@{option A}≡) ==> (≡{n}@{option B}≡)) mbind.
Proof. destruct 2; simpl; auto. Qed.
Global Instance option_mjoin_ne {SI : sidx} {A : ofe} n :
  Proper (dist n ==> (≡{n}@{option A}≡)) mjoin.
Proof. destruct 1 as [?? []|]; simpl; by constructor. Qed.

Global Instance option_fmap_dist_inj {SI : sidx} {A B : ofe} (f : A → B) n :
  Inj (≡{n}≡) (≡{n}≡) f → Inj (≡{n}@{option A}≡) (≡{n}@{option B}≡) (fmap f).
Proof. apply option_fmap_inj. Qed.

Lemma fmap_Some_dist {SI : sidx}
    {A B : ofe} (f : A → B) (mx : option A) (y : B) n :
  f <$> mx ≡{n}≡ Some y ↔ ∃ x : A, mx = Some x ∧ y ≡{n}≡ f x.
Proof.
  split; [|by intros (x&->&->)].
  intros (?&?%fmap_Some&?)%dist_Some_inv_r'; naive_solver.
Qed.

Definition optionO_map {SI : sidx} {A B: ofe} (f : A -n> B) :
    optionO A -n> optionO B :=
  OfeMor (fmap f : optionO A → optionO B).
Global Instance optionO_map_ne {SI : sidx} (A B: ofe) :
  NonExpansive (@optionO_map SI A B).
Proof. by intros n f f' Hf []; constructor; apply Hf. Qed.

Program Definition optionOF {SI : sidx} (F : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := optionO (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := optionO_map (oFunctor_map F fg)
|}.
Next Obligation.
  intros ? F A1 ? A2 ? B1 ? B2 ? n f g Hfg;
    by apply optionO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros ? F A ? B ? x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=> y; apply oFunctor_map_id.
Qed.
Next Obligation.
  intros ? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x.
  rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=> y; apply oFunctor_map_compose.
Qed.

Global Instance optionOF_contractive {SI : sidx} F :
  oFunctorContractive F → oFunctorContractive (optionOF F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
    apply optionO_map_ne, oFunctor_map_contractive.
Qed.

(** * Later type *)
(** Note that the projection [later_car] is not non-expansive (see also the
lemma [later_car_anti_contractive] below), so it cannot be used in the logic.
If you need to get a witness out, you should use the lemma [Next_uninj]
instead. *)
Record later (A : Type) : Type := Next { later_car : A }.
Add Printing Constructor later.
Global Arguments Next {_} _.
Global Arguments later_car {_} _.
Global Instance: Params (@Next) 1 := {}.

Section later.
  Context {SI : sidx} {A : ofe}.

  Local Instance later_equiv : Equiv (later A) := λ x y, later_car x ≡ later_car y.
  Local Instance later_dist : Dist (later A) := λ n x y,
    dist_later n (later_car x) (later_car y).

  Definition later_ofe_mixin : OfeMixin (later A).
  Proof.
    split.
    - intros [x] [y]; unfold equiv, later_equiv; rewrite !equiv_dist.
      split; first by intros Hxy n; split; intros m Hm.
      intros H n. eapply (H (Sᵢ n)), SIdx.lt_succ_diag_r.
    - split; rewrite /dist /later_dist.
      + by intros [x].
      + by intros [x] [y].
      + by intros [x] [y] [z] ??; trans y.
    - intros n m [x] [y] Hxy ?; split; intros p Hp.
      by eapply Hxy, SIdx.lt_le_trans.
  Qed.
  Canonical Structure laterO : ofe := Ofe (later A) later_ofe_mixin.

  Global Instance Next_contractive : Contractive (@Next A).
  Proof. by intros n x y. Qed.
  Global Instance Next_inj n : Inj (dist_later n) (dist n) (@Next A).
  Proof. by intros x y H. Qed.
  Lemma Next_uninj x : ∃ a, x ≡ Next a.
  Proof. by exists (later_car x). Qed.
  Local Instance later_car_anti_contractive n :
    Proper (dist n ==> dist_later n) later_car.
  Proof. move=> [x] [y] /= Hxy. done. Qed.

  Program Definition later_chain (c : chain laterO) : chain A :=
    {| chain_car n := later_car (c (Sᵢ n)) |}.
  Next Obligation.
    intros c n i ?%SIdx.succ_le_mono.
    apply (chain_cauchy c (Sᵢ n)); eauto using SIdx.lt_succ_diag_r.
  Qed.
  Program Definition later_limit_bchain {n} (c : bchain laterO n)
      (Hn : SIdx.limit n) : bchain A n :=
    {| bchain_car m Hm := later_car (c (Sᵢ m) _) |}.
  Next Obligation. intros n _ Hn. apply Hn. Qed.
  Next Obligation.
    intros n c Hn m p ???%SIdx.succ_le_mono; simpl.
    apply (bchain_cauchy n c (Sᵢ m) (Sᵢ p)); eauto using SIdx.lt_succ_diag_r.
  Qed.

  Global Program Instance later_cofe `{!Cofe A} : Cofe laterO := {
    compl c := Next (compl (later_chain c));
    lbcompl n Hn c := Next (lbcompl Hn (later_limit_bchain c Hn))
  }.
  Next Obligation.
    intros ? n c; split; intros m Hm%SIdx.le_succ_l; simpl. rewrite conv_compl /=.
    symmetry; apply (chain_cauchy c (Sᵢ m) n); eauto using SIdx.lt_succ_diag_r.
  Qed.
  Next Obligation.
    intros ? n ? c m Hm; simpl; split; intros p Hp; simpl.
    rewrite (conv_lbcompl _ _ (transitivity Hp Hm)) /=.
    symmetry; eapply (bchain_cauchy n c (Sᵢ p)); eauto using SIdx.lt_succ_diag_r.
    by apply SIdx.le_succ_l.
  Qed.
  Next Obligation.
    intros ? n Hn c1 c2 m Hc; split; intros p Hp; simpl.
    apply lbcompl_ne=> q Hq; by apply Hc.
  Qed.

  (** [f] is contractive iff it can factor into [Next] and a non-expansive
  function. *)
  Lemma contractive_alt {B : ofe} (f : A → B) :
    Contractive f ↔ ∃ g : later A → B, NonExpansive g ∧ ∀ x, f x ≡ g (Next x).
  Proof.
    split.
    - intros Hf. exists (f ∘ later_car); split=> // n x y ?. by f_equiv.
    - intros (g&Hg&Hf) n x y Hxy. rewrite !Hf. by apply Hg.
  Qed.
End later.

Global Arguments laterO {_} _.

Definition later_map {A B} (f : A → B) (x : later A) : later B :=
  Next (f (later_car x)).
Global Instance later_map_ne {SI : sidx} {A B : ofe} (f : A → B) n :
  Proper (dist_later n ==> dist_later n) f →
  Proper (dist n ==> dist n) (later_map f) | 0.
Proof.
  intros P [x] [y] H; rewrite /later_map //=.
  split; intros m Hm; apply P, Hm. apply H.
Qed.

Global Instance later_map_ne' {SI : sidx} {A B : ofe} (f : A → B) :
  NonExpansive f → NonExpansive (later_map f).
Proof.
  intros ?? [x] [y] H. unfold later_map; simpl.
  split; intros ??; simpl. f_equiv. by apply H.
Qed.

Global Instance later_map_proper {SI : sidx} {A B : ofe} (f : A → B) :
  Proper ((≡) ==> (≡)) f →
  Proper ((≡) ==> (≡)) (later_map f).
Proof. solve_proper. Qed.

Lemma later_map_Next {SI : sidx} {A B : ofe} (f : A → B) x :
  later_map f (Next x) = Next (f x).
Proof. done. Qed.
Lemma later_map_id {SI : sidx} {A} (x : later A) : later_map id x = x.
Proof. by destruct x. Qed.
Lemma later_map_compose {SI : sidx}
    {A B C} (f : A → B) (g : B → C) (x : later A) :
  later_map (g ∘ f) x = later_map g (later_map f x).
Proof. by destruct x. Qed.
Lemma later_map_ext {SI : sidx} {A B : ofe} (f g : A → B) x :
  (∀ x, f x ≡ g x) → later_map f x ≡ later_map g x.
Proof. destruct x; intros Hf; apply Hf. Qed.
Definition laterO_map {SI : sidx}
    {A B: ofe} (f : A -n> B) : laterO A -n> laterO B :=
  OfeMor (later_map f).
Global Instance laterO_map_contractive {SI : sidx} (A B : ofe) :
  Contractive (@laterO_map SI A B).
Proof. intros n f g Hlater [x]; split; intros ??; simpl. by apply Hlater. Qed.

Program Definition laterOF {SI : sidx} (F : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := laterO (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := laterO_map (oFunctor_map F fg)
|}.
Next Obligation.
  intros ? F A1 ? A2 ? B1 ? B2 ? n fg fg' ?.
  by apply (contractive_ne laterO_map), oFunctor_map_ne.
Qed.
Next Obligation.
  intros ? F A ? B ? x; simpl. rewrite -{2}(later_map_id x).
  apply later_map_ext=>y. by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros ? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl. rewrite -later_map_compose.
  apply later_map_ext=>y; apply oFunctor_map_compose.
Qed.
Notation "▶ F"  := (laterOF F%OF) (at level 20, right associativity) : oFunctor_scope.

Global Instance laterOF_contractive {SI : sidx} F : oFunctorContractive (laterOF F).
Proof.
  intros A1 ? A2 ? B1 ? B2 ? n fg fg' Hfg. apply laterO_map_contractive.
  split; intros ???; simpl. by eapply oFunctor_map_ne, Hfg.
Qed.

(** * Dependently-typed functions over a discrete domain *)
(** This separate notion is useful whenever we need dependent functions, and
whenever we want to avoid the hassle of the bundled non-expansive function type.

Note that non-dependent functions over a discrete domain, [A -d> B] (following
the notation we introduce below) are non-expansive if they are
[Proper ((≡) ==> (≡))]. In other words, since the domain is discrete,
non-expansiveness and respecting [(≡)] are the same. If the domain is moreover
Leibniz ([LeibnizEquiv A]), we get both for free.

We make [discrete_fun] a definition so that we can register it as a canonical
structure.  We do not bundle the [Proper] proof to keep [discrete_fun] easier to
use. It turns out all the desired OFE and functorial properties do not rely on
this [Proper] instance. *)
Definition discrete_fun {SI : sidx} {A} (B : A → ofe) := ∀ x : A, B x.

Section discrete_fun.
  Context {SI : sidx} {A : Type} {B : A → ofe}.
  Implicit Types f g : discrete_fun B.

  Local Instance discrete_fun_equiv : Equiv (discrete_fun B) := λ f g, ∀ x, f x ≡ g x.
  Local Instance discrete_fun_dist : Dist (discrete_fun B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition discrete_fun_ofe_mixin : OfeMixin (discrete_fun B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - intros n m f g ? H x. by eapply dist_le.
  Qed.
  Canonical Structure discrete_funO := Ofe (discrete_fun B) discrete_fun_ofe_mixin.

  Program Definition discrete_fun_chain (c : chain discrete_funO)
    (x : A) : chain (B x) := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Program Definition discrete_fun_bchain {n} (c : bchain discrete_funO n)
    (x : A) : bchain (B x) n := {| bchain_car n Hn := c n Hn x |}.
  Next Obligation. intros n c x m p Hm Hp Hmp. by apply (bchain_cauchy n c). Qed.

  Global Program Instance discrete_fun_cofe `{!∀ x, Cofe (B x)} :
      Cofe discrete_funO := {
    compl c x := compl (discrete_fun_chain c x);
    lbcompl n Hn c x := lbcompl Hn (discrete_fun_bchain c x)
  }.
  Next Obligation. intros ? n c x. by apply conv_compl. Qed.
  Next Obligation. intros ? n Hn c m Hm x. by rewrite (conv_lbcompl _ _ Hm). Qed.
  Next Obligation.
    intros ? n Hn c1 c2 m Hc x. apply lbcompl_ne=> ?? /=. by apply Hc.
  Qed.

  Global Instance discrete_fun_lookup_discrete `{EqDecision A} f x :
    Discrete f → Discrete (f x).
  Proof.
    intros Hf y ?.
    set (g x' := if decide (x = x') is left H then eq_rect _ B y _ H else f x').
    trans (g x).
    { apply Hf=> x'. unfold g. by destruct (decide _) as [[]|]. }
    unfold g. destruct (decide _) as [Hx|]; last done.
    by rewrite (proof_irrel Hx eq_refl).
  Qed.
End discrete_fun.

Global Arguments discrete_funO {_ _} _.
Notation "A -d> B" :=
  (@discrete_funO _ A (λ _, B)) (at level 99, B at level 200, right associativity).

Definition discrete_fun_map {SI : sidx} {A} {B1 B2 : A → ofe} (f : ∀ x, B1 x → B2 x)
  (g : discrete_fun B1) : discrete_fun B2 := λ x, f _ (g x).

Lemma discrete_fun_map_ext {SI : sidx} {A} {B1 B2 : A → ofe} (f1 f2 : ∀ x, B1 x → B2 x)
  (g : discrete_fun B1) :
  (∀ x, f1 x (g x) ≡ f2 x (g x)) → discrete_fun_map f1 g ≡ discrete_fun_map f2 g.
Proof. done. Qed.
Lemma discrete_fun_map_id {SI : sidx} {A} {B : A → ofe} (g : discrete_fun B) :
  discrete_fun_map (λ _, id) g = g.
Proof. done. Qed.
Lemma discrete_fun_map_compose {SI : sidx} {A} {B1 B2 B3 : A → ofe}
    (f1 : ∀ x, B1 x → B2 x) (f2 : ∀ x, B2 x → B3 x) (g : discrete_fun B1) :
  discrete_fun_map (λ x, f2 x ∘ f1 x) g = discrete_fun_map f2 (discrete_fun_map f1 g).
Proof. done. Qed.

Global Instance discrete_fun_map_ne {SI : sidx} {A} {B1 B2 : A → ofe}
    (f : ∀ x, B1 x → B2 x) n :
  (∀ x, Proper (dist n ==> dist n) (f x)) →
  Proper (dist n ==> dist n) (discrete_fun_map f).
Proof. by intros ? y1 y2 Hy x; rewrite /discrete_fun_map (Hy x). Qed.

Definition discrete_funO_map {SI : sidx} {A} {B1 B2 : A → ofe}
    (f : discrete_fun (λ x, B1 x -n> B2 x)) :
  discrete_funO B1 -n> discrete_funO B2 := OfeMor (discrete_fun_map f).
Global Instance discrete_funO_map_ne {SI : sidx} {A} {B1 B2 : A → ofe} :
  NonExpansive (@discrete_funO_map SI A B1 B2).
Proof. intros n f1 f2 Hf g x; apply Hf. Qed.

Program Definition discrete_funOF {SI : sidx} {C} (F : C → oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := discrete_funO (λ c, oFunctor_car (F c) A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := discrete_funO_map (λ c, oFunctor_map (F c) fg)
|}.
Next Obligation.
  intros ? C F A1 ? A2 ? B1 ? B2 ? n ?? g.
  by apply discrete_funO_map_ne=>?; apply oFunctor_map_ne.
Qed.
Next Obligation.
  intros ? C F A ? B ? g; simpl. rewrite -{2}(discrete_fun_map_id g).
  apply discrete_fun_map_ext=> y; apply oFunctor_map_id.
Qed.
Next Obligation.
  intros ? C F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f1 f2 f1' f2' g.
  rewrite /= -discrete_fun_map_compose.
  apply discrete_fun_map_ext=>y; apply oFunctor_map_compose.
Qed.

Notation "T -d> F" := (@discrete_funOF _ T%type (λ _, F%OF)) : oFunctor_scope.

Global Instance discrete_funOF_contractive {SI : sidx} {C} (F : C → oFunctor) :
  (∀ c, oFunctorContractive (F c)) → oFunctorContractive (discrete_funOF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n ?? g.
  by apply discrete_funO_map_ne=>c; apply oFunctor_map_contractive.
Qed.

(** * Constructing isomorphic OFEs *)
Lemma iso_ofe_mixin {SI : sidx}
  {A : ofe} {B : Type} `{!Equiv B, !Dist B} (g : B → A)
  (g_equiv : ∀ y1 y2, y1 ≡ y2 ↔ g y1 ≡ g y2)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2) : OfeMixin B.
Proof.
  split.
  - intros y1 y2. rewrite g_equiv. setoid_rewrite g_dist. apply equiv_dist.
  - split.
    + intros y. by apply g_dist.
    + intros y1 y2. by rewrite !g_dist.
    + intros y1 y2 y3. rewrite !g_dist. intros ??; etrans; eauto.
  - intros n m y1 y2. rewrite !g_dist. by eapply dist_le.
Qed.

Section iso_cofe_subtype.
  Context {SI : sidx} {A B : ofe} `{!Cofe A}.
  Context (P : A → Prop) (f : ∀ x, P x → B) (g : B → A).
  Context (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2).

  Let Hgne : NonExpansive g.
  Proof. intros n y1 y2. apply g_dist. Defined.
  Local Existing Instance Hgne.

  Context (gf : ∀ x Hx, g (f x Hx) ≡ x).
  Context (Hlimit : ∀ c : chain B, P (compl (chain_map g c))).
  Context (Hblimit : ∀ n (Hn : SIdx.limit n) c, P (lbcompl Hn (bchain_map g c))).

  Program Definition iso_cofe_subtype : Cofe B := {|
    compl c := f (compl (chain_map g c)) _;
    lbcompl n Hn c := f (lbcompl Hn (bchain_map g c)) _
  |}.
  Next Obligation. apply Hlimit. Qed.
  Next Obligation. apply Hblimit. Qed.
  Next Obligation. intros n c; simpl. apply g_dist. by rewrite gf conv_compl. Qed.
  Next Obligation.
    intros n Hn c m Hm; simpl. apply g_dist. by rewrite gf (conv_lbcompl _ _ Hm).
  Qed.
  Next Obligation.
    intros n Hn c1 c2 m Hc; simpl. apply g_dist. rewrite !gf.
    apply lbcompl_ne=> ?? /=. by rewrite Hc.
  Qed.
End iso_cofe_subtype.

Lemma iso_cofe_subtype' {SI : sidx} {A B : ofe} `{!Cofe A}
  (P : A → Prop) (f : ∀ x, P x → B) (g : B → A)
  (Pg : ∀ y, P (g y))
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x Hx, g (f x Hx) ≡ x)
  (Hlimit : LimitPreserving P) : Cofe B.
Proof. destruct Hlimit. apply: (iso_cofe_subtype P f g); eauto. Qed.

Definition iso_cofe {SI : sidx} {A B : ofe} `{!Cofe A} (f : A → B) (g : B → A)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x, g (f x) ≡ x) : Cofe B.
Proof. by apply (iso_cofe_subtype (λ _, True) (λ x _, f x) g). Qed.

(** * Sigma type *)
Section sigma.
  Context {SI : sidx} {A : ofe} {P : A → Prop}.
  Implicit Types x : sig P.

  (* TODO: Find a better place for this Equiv instance. It also
     should not depend on A being an OFE. *)
  Local Instance sig_equiv : Equiv (sig P) := λ x1 x2, `x1 ≡ `x2.
  Local Instance sig_dist : Dist (sig P) := λ n x1 x2, `x1 ≡{n}≡ `x2.

  Definition sig_equiv_def x y : (x ≡ y) = (`x ≡ `y) := reflexivity _.
  Definition sig_dist_def n x y : (x ≡{n}≡ y) = (`x ≡{n}≡ `y) := reflexivity _.

  Lemma exist_ne n a1 a2 (H1 : P a1) (H2 : P a2) :
    a1 ≡{n}≡ a2 → a1 ↾ H1 ≡{n}≡ a2 ↾ H2.
  Proof. done. Qed.

  Global Instance proj1_sig_ne : NonExpansive (@proj1_sig _ P).
  Proof. by intros n [a Ha] [b Hb] ?. Qed.
  Definition sig_ofe_mixin : OfeMixin (sig P).
  Proof. by apply (iso_ofe_mixin proj1_sig). Qed.
  Canonical Structure sigO : ofe := Ofe (sig P) sig_ofe_mixin.

  Global Instance sig_cofe `{!Cofe A, !LimitPreserving P} : Cofe sigO.
  Proof. apply (iso_cofe_subtype' P (exist P) proj1_sig)=> //. by intros []. Qed.

  Global Instance sig_discrete (x : sig P) :  Discrete (`x) → Discrete x.
  Proof. intros ? y. rewrite sig_dist_def sig_equiv_def. apply (discrete_0 _). Qed.
  Global Instance sig_ofe_discrete : OfeDiscrete A → OfeDiscrete sigO.
  Proof. intros ??. apply _. Qed.
End sigma.

Global Arguments sigO {_ _} _.

(** * SigmaT type *)
(** Ofe for [sigT]. The first component must be discrete and use Leibniz
equality, while the second component might be any OFE. *)
Section sigT.
  Import EqNotations.

  Context {SI : sidx} {A : Type} {P : A → ofe}.
  Implicit Types x : sigT P.

  (**
    The distance for [{ a : A & P }] uses Leibniz equality on [A] to
    transport the second components to the same type,
    and then step-indexed distance on the second component.
    Unlike in the topos of trees, with (C)OFEs we cannot use step-indexed equality
    on the first component.
  *)
  Local Instance sigT_dist : Dist (sigT P) := λ n x1 x2,
    ∃ Heq : projT1 x1 = projT1 x2, rew Heq in projT2 x1 ≡{n}≡ projT2 x2.

  (**
    Usually we'd give a direct definition, and show it equivalent to
    [∀ n, x1 ≡{n}≡ x2] when proving the [equiv_dist] OFE axiom.
    But here the equivalence requires UIP — see [sigT_equiv_eq_alt].
    By defining [equiv] in terms of [dist], we can define an OFE
    without assuming UIP, at the cost of complex reasoning on [equiv].
  *)
  Local Instance sigT_equiv : Equiv (sigT P) := λ x1 x2,
    ∀ n, x1 ≡{n}≡ x2.

  (** Unfolding lemmas.
      Written with [↔] not [=] to avoid https://github.com/rocq-prover/rocq/issues/3814. *)
  Definition sigT_equiv_eq x1 x2 : (x1 ≡ x2) ↔ ∀ n, x1 ≡{n}≡ x2 :=
      reflexivity _.

  Definition sigT_dist_eq x1 x2 n : (x1 ≡{n}≡ x2) ↔
    ∃ Heq : projT1 x1 = projT1 x2, (rew Heq in projT2 x1) ≡{n}≡ projT2 x2 :=
      reflexivity _.

  Definition sigT_dist_proj1 n {x y} :
    x ≡{n}≡ y → projT1 x = projT1 y := proj1_ex.
  Definition sigT_equiv_proj1 {x y} :
    x ≡ y → projT1 x = projT1 y := λ H, proj1_ex (H 0ᵢ).

  Definition sigT_ofe_mixin : OfeMixin (sigT P).
  Proof.
    split => // n.
    - split; hnf; setoid_rewrite sigT_dist_eq.
      + intros. by exists eq_refl.
      + move => [xa x] [ya y] /=. destruct 1 as [-> Heq].
        by exists eq_refl.
      + move => [xa x] [ya y] [za z] /=.
        destruct 1 as [-> Heq1].
        destruct 1 as [-> Heq2]. exists eq_refl => /=. by trans y.
    - setoid_rewrite sigT_dist_eq.
      move => m [xa x] [ya y] /=. destruct 1 as [-> Heq].
      exists eq_refl. eauto using dist_le.
  Qed.

  Canonical Structure sigTO : ofe := Ofe (sigT P) sigT_ofe_mixin.

  Lemma sigT_equiv_eq_alt `{!∀ a b : A, ProofIrrel (a = b)} x1 x2 :
    x1 ≡ x2 ↔
    ∃ Heq : projT1 x1 = projT1 x2, rew Heq in projT2 x1 ≡ projT2 x2.
  Proof.
    setoid_rewrite equiv_dist. setoid_rewrite sigT_dist_eq. split => Heq.
    - move: (Heq 0ᵢ) => [H0eq1 _].
      exists H0eq1 => n. move: (Heq n) => [] Hneq1.
      by rewrite (proof_irrel H0eq1 Hneq1).
    - move: Heq => [Heq1 Heqn2] n. by exists Heq1.
  Qed.

  (** [projT1] is non-expansive and proper. *)
  Global Instance projT1_ne : NonExpansive (projT1 : sigTO → leibnizO A).
  Proof. solve_proper. Qed.

  Global Instance projT1_proper : Proper ((≡) ==> (≡)) (projT1 : sigTO → leibnizO A).
  Proof. apply ne_proper, projT1_ne. Qed.

  (** [projT2] is "non-expansive"; the properness lemma [projT2_ne] requires UIP. *)
  Lemma projT2_ne n (x1 x2 : sigTO) (Heq : x1 ≡{n}≡ x2) :
    rew (sigT_dist_proj1 n Heq) in projT2 x1 ≡{n}≡ projT2 x2.
  Proof. by destruct Heq. Qed.

  Lemma projT2_proper `{!∀ a b : A, ProofIrrel (a = b)} (x1 x2 : sigTO) (Heqs : x1 ≡ x2):
    rew (sigT_equiv_proj1 Heqs) in projT2 x1 ≡ projT2 x2.
  Proof.
    move: x1 x2 Heqs => [a1 x1] [a2 x2] Heqs.
    case: (proj1 (sigT_equiv_eq_alt _ _) Heqs) => /=. intros ->.
    rewrite (proof_irrel (sigT_equiv_proj1 Heqs) eq_refl) /=. done.
  Qed.

  (** [existT] is "non-expansive" — general, dependently-typed statement. *)
  Lemma existT_ne n {i1 i2} {v1 : P i1} {v2 : P i2} :
    ∀ (Heq : i1 = i2), (rew f_equal P Heq in v1 ≡{n}≡ v2) →
      existT i1 v1 ≡{n}≡ existT i2 v2.
  Proof. intros ->; simpl. exists eq_refl => /=. done. Qed.

  Lemma existT_proper {i1 i2} {v1 : P i1} {v2 : P i2} :
    ∀ (Heq : i1 = i2), (rew f_equal P Heq in v1 ≡ v2) →
      existT i1 v1 ≡ existT i2 v2.
  Proof. intros Heq Heqv n. apply (existT_ne n Heq), equiv_dist, Heqv. Qed.

  (** [existT] is "non-expansive" — non-dependently-typed version. *)
  Global Instance existT_ne_2 a : NonExpansive (@existT A P a).
  Proof. move => ??? Heq. apply (existT_ne _ eq_refl Heq). Qed.

  Global Instance existT_proper_2 a : Proper ((≡) ==> (≡)) (@existT A P a).
  Proof. apply ne_proper, _. Qed.

  Implicit Types c : chain sigTO.

  Global Instance sigT_discrete x : Discrete (projT2 x) → Discrete x.
  Proof.
    move: x => [xa x] ? [ya y] [] /=; intros -> => /= Hxy n.
    exists eq_refl => /=. apply equiv_dist, (discrete_0 _), Hxy.
  Qed.

  Global Instance sigT_ofe_discrete : (∀ a, OfeDiscrete (P a)) → OfeDiscrete sigTO.
  Proof. intros ??. apply _. Qed.

  Lemma sigT_chain_const_proj1 c n : projT1 (c n) = projT1 (c 0ᵢ).
  Proof.
    refine (sigT_dist_proj1 _ (chain_cauchy c 0ᵢ n _)). apply SIdx.le_0_l.
  Qed.

  Lemma sigT_bchain_const_proj1 n Hn (c: bchain sigTO n) m Hm :
    projT1 (c m Hm) = projT1 (c 0ᵢ Hn).
  Proof.
    refine (sigT_dist_proj1 _ (bchain_cauchy n c 0ᵢ m _ _ _)). apply SIdx.le_0_l.
  Qed.

  (** For this COFE construction we need UIP (Uniqueness of Identity Proofs)
  on [A] (i.e. [∀ x y : A, ProofIrrel (x = y)]. UIP is most commonly obtained
  from decidable equality (by Hedberg’s theorem, see
  [stdpp.proof_irrel.eq_pi]). *)
  Section cofe.
    Context `{!∀ a b : A, ProofIrrel (a = b)} `{!∀ a, Cofe (P a)}.

    (** The definitions [sigT_compl] and [sigT_lbcompl] are similar to
    [sum_compl] and [sum_bcompl]. We are given a [chain (sigT P)], i.e., a
    sequence of dependent pairs [existT x_i y_i], but know that all [x_i]s are
    the same. So, given a [chain (sigT P)], we are able to construct a
    [chain (P (projT1 (c 0ᵢ)))] (which involves some programming with dependent
    types), which we can then give to the [compl] operation on [P]. *)
    Program Definition chain_map_snd c : chain (P (projT1 (c 0ᵢ))) :=
      {| chain_car n := rew (sigT_chain_const_proj1 c n) in projT2 (c n) |}.
    Next Obligation.
      move => c n i Hle /=.
      (* [Hgoal] is our thesis, up to casts: *)
      case: (chain_cauchy c n i Hle) => [Heqin Hgoal] /=.
      (* Pretty delicate. We have two casts to [projT1 (c 0ᵢ)].
        We replace those by one cast. *)
      move: (sigT_chain_const_proj1 c i) (sigT_chain_const_proj1 c n)
        => Heqi0 Heqn0.
      (* Rewrite [projT1 (c 0ᵢ)] to [projT1 (c n)] in goal and [Heqi0]: *)
      destruct Heqn0.
      by rewrite /= (proof_irrel Heqi0 Heqin).
    Qed.

    Definition sigT_compl : Compl sigTO := λ c,
      existT (projT1 (c 0ᵢ)) (compl (chain_map_snd c)).

    Program Definition bchain_map_snd n Hn (c : bchain sigTO n) :
        bchain (P (projT1 (c 0ᵢ Hn))) n :=
      {| bchain_car m Hm :=
        rew (sigT_bchain_const_proj1 n Hn c m Hm) in projT2 (c m Hm) |}.
    Next Obligation.
      move => n Hn c m p Hm Hp Hle /=.
      (* [Hgoal] is our thesis, up to casts: *)
      case: (bchain_cauchy n c m p Hm Hp Hle) => [Heqin Hgoal] /=.
      (* Pretty delicate. We have two casts to [projT1 (c 0ᵢ)].
        We replace those by one cast. *)
      move: (sigT_bchain_const_proj1 n Hn c m Hm)
        (sigT_bchain_const_proj1 n Hn c p Hp)=> Heqm0 Heqp0.
      (* Rewrite [projT1 (c 0ᵢ)] to [projT1 (c n)] in goal and [Heqi0]: *)
      destruct Heqm0.
      by rewrite /= (proof_irrel Heqp0 Heqin).
    Qed.

    Definition sigT_lbcompl : LBCompl sigTO := λ n Hn (c : bchain sigTO n),
      existT (projT1 (c _ (SIdx.limit_lt_0 _ Hn)))
             (lbcompl Hn (bchain_map_snd n (SIdx.limit_lt_0 _ Hn) c)).

    Global Program Instance sigT_cofe : Cofe sigTO :=
      { compl := sigT_compl; lbcompl := sigT_lbcompl }.
    Next Obligation.
      intros n c. rewrite /sigT_compl sigT_dist_eq /=.
      exists (symmetry (sigT_chain_const_proj1 c n)).
      (* Our thesis, up to casts: *)
      pose proof (conv_compl n (chain_map_snd c)) as Hgoal.
      move: (compl (chain_map_snd c)) Hgoal => pc0 /=.
      by destruct (sigT_chain_const_proj1 c n).
    Qed.
    Next Obligation.
      intros n Hn c m Hm. rewrite /sigT_lbcompl sigT_dist_eq /=.
      exists (symmetry (sigT_bchain_const_proj1 n (SIdx.limit_lt_0 _ Hn) c m Hm)).
      (* Our thesis, up to casts: *)
      pose proof (conv_lbcompl Hn
        (bchain_map_snd n (SIdx.limit_lt_0 _ Hn) c) Hm) as Hgoal.
      move: (lbcompl Hn (bchain_map_snd n _ c)) Hgoal => pc0 /=.
      by destruct (sigT_bchain_const_proj1 n _ c m Hm).
    Qed.
    Next Obligation.
      intros n Hn c1 c2 m Hc. rewrite /sigT_lbcompl sigT_dist_eq /=.
      destruct (Hc 0ᵢ (SIdx.limit_lt_0 _ Hn)) as [eq Ht]. exists eq; simpl.
      enough (lbcompl Hn (rew [λ x : A, bchain (P x) n] eq in
                          bchain_map_snd n (SIdx.limit_lt_0 _ Hn) c1)
        ≡{m}≡ lbcompl Hn (bchain_map_snd n (SIdx.limit_lt_0 _ Hn) c2)) as Hlbcompl.
      { rewrite -Hlbcompl. clear Ht Hlbcompl. by destruct eq. }
      apply lbcompl_ne=> p Hp /=. destruct (Hc p Hp) as [eq' H'].
      rewrite -(@map_subst _ (λ y, bchain (P y) n) P (λ y d, d p Hp) _ _ eq) /=.
      rewrite rew_compose. revert H'.
      move: (sigT_bchain_const_proj1 n _ c2 p Hp)
        (eq_trans (sigT_bchain_const_proj1 n _ c1 p Hp) eq)=> e1 e2.
      destruct e1; simpl. intros <-. by rewrite /= (proof_irrel e2 eq').
    Qed.
  End cofe.
End sigT.

Global Arguments sigTO {_ _} _.

Section sigTOF.
  Context {SI : sidx} {A : Type}.

  Program Definition sigT_map {P1 P2 : A → ofe} :
    discrete_funO (λ a, P1 a -n> P2 a) -n>
    sigTO P1 -n> sigTO P2 :=
    λne f xpx, existT _ (f _ (projT2 xpx)).
  Next Obligation.
    move => ?? f n [x px] [y py] [/= Heq]. destruct Heq; simpl.
    exists eq_refl => /=. by f_equiv.
  Qed.
  Next Obligation.
    move => ?? n f g Heq [x px] /=. exists eq_refl => /=. apply Heq.
  Qed.

  Program Definition sigTOF (F : A → oFunctor) : oFunctor := {|
    oFunctor_car A CA B CB := sigTO (λ a, oFunctor_car (F a) A B);
    oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := sigT_map (λ a, oFunctor_map (F a) fg)
  |}.
  Next Obligation.
    repeat intro. exists eq_refl => /=. solve_proper.
  Qed.
  Next Obligation.
    simpl; intros. apply (existT_proper eq_refl), oFunctor_map_id.
  Qed.
  Next Obligation.
    simpl; intros. apply (existT_proper eq_refl), oFunctor_map_compose.
  Qed.

  Global Instance sigTOF_contractive {F} :
    (∀ a, oFunctorContractive (F a)) → oFunctorContractive (sigTOF F).
  Proof.
    repeat intro. apply sigT_map => a. exact: oFunctor_map_contractive.
  Qed.
End sigTOF.

Global Arguments sigTOF {_ _} _%_OF.

Notation "{ x  &  P }" := (sigTOF (λ x, P%OF)) : oFunctor_scope.
Notation "{ x : A &  P }" := (@sigTOF _ A%type (λ x, P%OF)) : oFunctor_scope.

(** * Isomorphisms between OFEs *)
Record ofe_iso {SI : sidx} (A B : ofe) := OfeIso {
  ofe_iso_1 : A -n> B;
  ofe_iso_2 : B -n> A;
  ofe_iso_12 y : ofe_iso_1 (ofe_iso_2 y) ≡ y;
  ofe_iso_21 x : ofe_iso_2 (ofe_iso_1 x) ≡ x;
}.
Global Arguments OfeIso {_ _ _} _ _ _ _.
Global Arguments ofe_iso_1 {_ _ _} _.
Global Arguments ofe_iso_2 {_ _ _} _.
Global Arguments ofe_iso_12 {_ _ _} _ _.
Global Arguments ofe_iso_21 {_ _ _} _ _.

Section ofe_iso.
  Context {SI : sidx} {A B : ofe}.

  Local Instance ofe_iso_equiv : Equiv (ofe_iso A B) := λ I1 I2,
    ofe_iso_1 I1 ≡ ofe_iso_1 I2 ∧ ofe_iso_2 I1 ≡ ofe_iso_2 I2.

  Local Instance ofe_iso_dist : Dist (ofe_iso A B) := λ n I1 I2,
    ofe_iso_1 I1 ≡{n}≡ ofe_iso_1 I2 ∧ ofe_iso_2 I1 ≡{n}≡ ofe_iso_2 I2.

  Global Instance ofe_iso_1_ne : NonExpansive (ofe_iso_1 (A:=A) (B:=B)).
  Proof. by destruct 1. Qed.
  Global Instance ofe_iso_2_ne : NonExpansive (ofe_iso_2 (A:=A) (B:=B)).
  Proof. by destruct 1. Qed.

  Lemma ofe_iso_ofe_mixin : OfeMixin (ofe_iso A B).
  Proof. by apply (iso_ofe_mixin (λ I, (ofe_iso_1 I, ofe_iso_2 I))). Qed.
  Canonical Structure ofe_isoO : ofe := Ofe (ofe_iso A B) ofe_iso_ofe_mixin.

  Global Instance ofe_iso_cofe `{!SIdxFinite SI}
    `{!Cofe A, !Cofe B} : Cofe ofe_isoO.
  Proof.
    apply (iso_cofe_subtype'
      (λ I : prodO (A -n> B) (B -n> A),
        (∀ y, I.1 (I.2 y) ≡ y) ∧ (∀ x, I.2 (I.1 x) ≡ x))
      (λ I HI, OfeIso (I.1) (I.2) (proj1 HI) (proj2 HI))
      (λ I, (ofe_iso_1 I, ofe_iso_2 I))); [by intros []|done..|].
    apply limit_preserving_and; apply limit_preserving_forall=> ?;
      apply limit_preserving_equiv; solve_proper.
  Qed.
End ofe_iso.

Global Arguments ofe_isoO {_} _ _.

Program Definition iso_ofe_refl {SI : sidx} {A: ofe} : ofe_iso A A :=
  OfeIso cid cid _ _.
Solve Obligations with done.

Definition iso_ofe_sym {SI : sidx} {A B : ofe} (I : ofe_iso A B) : ofe_iso B A :=
  OfeIso (ofe_iso_2 I) (ofe_iso_1 I) (ofe_iso_21 I) (ofe_iso_12 I).
Global Instance iso_ofe_sym_ne {SI : sidx} {A B : ofe} :
  NonExpansive (iso_ofe_sym (A:=A) (B:=B)).
Proof. intros n I1 I2 []; split; simpl; by f_equiv. Qed.

Program Definition iso_ofe_trans {SI : sidx} {A B C: ofe}
    (I : ofe_iso A B) (J : ofe_iso B C) : ofe_iso A C :=
  OfeIso (ofe_iso_1 J ◎ ofe_iso_1 I) (ofe_iso_2 I ◎ ofe_iso_2 J) _ _.
Next Obligation. intros ? A B C I J z; simpl. by rewrite !ofe_iso_12. Qed.
Next Obligation. intros ? A B C I J z; simpl. by rewrite !ofe_iso_21. Qed.
Global Instance iso_ofe_trans_ne {SI : sidx} {A B C} :
  NonExpansive2 (iso_ofe_trans (A:=A) (B:=B) (C:=C)).
Proof. intros n I1 I2 [] J1 J2 []; split; simpl; by f_equiv. Qed.

Program Definition iso_ofe_cong {SI : sidx} (F : oFunctor) `{!Cofe A, !Cofe B}
    (I : ofe_iso A B) : ofe_iso (oFunctor_apply F A) (oFunctor_apply F B) :=
  OfeIso (oFunctor_map F (ofe_iso_2 I, ofe_iso_1 I))
    (oFunctor_map F (ofe_iso_1 I, ofe_iso_2 I)) _ _.
Next Obligation.
  intros ? F A ? B ? I x. rewrite -oFunctor_map_compose -{2}(oFunctor_map_id F x).
  apply equiv_dist=> n.
  apply oFunctor_map_ne; split=> ? /=; by rewrite ?ofe_iso_12 ?ofe_iso_21.
Qed.
Next Obligation.
  intros ? F A ? B ? I y. rewrite -oFunctor_map_compose -{2}(oFunctor_map_id F y).
  apply equiv_dist=> n.
  apply oFunctor_map_ne; split=> ? /=; by rewrite ?ofe_iso_12 ?ofe_iso_21.
Qed.
Global Instance iso_ofe_cong_ne {SI : sidx} (F : oFunctor) `{!Cofe A, !Cofe B} :
  NonExpansive (iso_ofe_cong F (A:=A) (B:=B)).
Proof. intros n I1 I2 []; split; simpl; by f_equiv. Qed.
Global Instance iso_ofe_cong_contractive {SI : sidx}
    (F : oFunctor) `{!Cofe A, !Cofe B} :
  oFunctorContractive F → Contractive (iso_ofe_cong F (A:=A) (B:=B)).
Proof. intros ? n I1 I2 HI; split; simpl; f_contractive; by destruct HI. Qed.
