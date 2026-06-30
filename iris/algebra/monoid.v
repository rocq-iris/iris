From iris.algebra Require Export ofe.

(** Important: If you define your own monoid, only declare a [Monoid] instance,
not a [MonoidOps] instance. *)

(** The [Monoid] class is used for the generic big operators in the file
[algebra/big_op]. The operation [o] and unit [u] are arguments instead of
fields of [Monoid] because we want to support multiple monoids over the same
carrier type (for example, on BIs we have monoids for [∗]/[emp], [∧]/[True],
and [∨]/[False]).

There are two classes, [MonoidOps] just groups the operation and unit, while
[Monoid] contains the laws. Definitions (e.g., the big operators) should use
[MonoidOps] so they do not depend on proofs, while lemmas should use [Monoid].
In definitions, the argument [o] is typically given, and [u] is an implicit
argument that is infered through search for a [MonoidOps] instance. Hence [o]
has input mode, and [u] output mode. *)
Class MonoidOps {M} (o : M → M → M) (u : M) := {}.
Global Hint Mode MonoidOps - ! - : typeclass_instances.

(** Note that [Monoid] has an argument [M : ofe]. We could in principle consider
monoids and big operators over setoids instead of OFEs. However, since we do not
have a canonical structure for setoids, we do not go that way.

Further note that we do not declare any of the projections as type class
instances (i.e., we use [:] instead of [::]). That is because we only need them
in the [big_op] file, and nowhere else. Hence, we declare these instances locally
there to avoid them being used elsewhere. *)
Class Monoid {SI : sidx} {M : ofe} (o : M → M → M) (u : M) := {
  monoid_ne : NonExpansive2 o;
  monoid_assoc : Assoc (≡) o;
  monoid_comm : Comm (≡) o;
  monoid_left_id : LeftId (≡) u o;
}.
Global Hint Mode Monoid - ! ! - : typeclass_instances.

(** This is the only instance for [MonoidOps] that should exist. *)
Global Instance monoid_ops {SI : sidx} `{Monoid M o u} : MonoidOps o u := {}.

Lemma monoid_proper {SI : sidx} `{Monoid M o u} : Proper ((≡) ==> (≡) ==> (≡)) o.
Proof. apply ne_proper_2, monoid_ne. Qed.
Lemma monoid_right_id {SI : sidx} `{Monoid M o u} : RightId (≡) u o.
Proof. intros x. etrans; [apply monoid_comm|apply monoid_left_id]. Qed.

(** The [Homomorphism] classes give rise to generic lemmas about big operators
commuting with each other. We also consider a [WeakMonoidHomomorphism] which
does not necessarily commute with unit; an example is the [own] connective: we
only have [True ==∗ own γ ∅], not [True ↔ own γ ∅]. *)
Class WeakMonoidHomomorphism {SI : sidx} {M1 M2 : ofe}
    (o1 : M1 → M1 → M1) (o2 : M2 → M2 → M2) {u1 u2} `{!Monoid o1 u1, !Monoid o2 u2}
    (R : relation M2) (f : M1 → M2) := {
  monoid_homomorphism_rel_po : PreOrder R;
  monoid_homomorphism_rel_proper : Proper ((≡) ==> (≡) ==> iff) R;
  monoid_homomorphism_op_proper : Proper (R ==> R ==> R) o2;
  monoid_homomorphism_ne : NonExpansive f;
  monoid_homomorphism x y : R (f (o1 x y)) (o2 (f x) (f y))
}.

Class MonoidHomomorphism {SI : sidx} {M1 M2 : ofe}
    (o1 : M1 → M1 → M1) (o2 : M2 → M2 → M2) {u1 u2} `{!Monoid o1 u1, !Monoid o2 u2}
    (R : relation M2) (f : M1 → M2) := {
  #[global] monoid_homomorphism_weak :: WeakMonoidHomomorphism o1 o2 R f;
  monoid_homomorphism_unit : R (f u1) u2
}.

Lemma weak_monoid_homomorphism_proper {SI : sidx}
  `{WeakMonoidHomomorphism M1 M2 o1 o2 u1 u2 R f} : Proper ((≡) ==> (≡)) f.
Proof. apply ne_proper, monoid_homomorphism_ne. Qed.
