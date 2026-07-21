From iris.algebra Require Import frac ufrac auth excl lib.gmap_view.
From iris.base_logic.lib Require Import invariants.

(* Should follow from [forall_inhabited] in std++, test that the the OFE
abstractions are actually unfolded by type class search. *)
Lemma discrete_fun_inhabited{SI : sidx} {A} (B : A → ofe)
  `{∀ x, Inhabited (B x)} : Inhabited (discrete_funO B).
Proof. apply _. Qed.

Section test_dist_equiv_mode.
  (* check that the mode for [Dist] does not trigger https://github.com/rocq-prover/rocq/issues/14441.
  From https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/700#note_69303. *)
  Lemma list_dist_lookup {A : ofe} n (l1 l2 : list A) :
    l1 ≡{n}≡ l2 ↔ ∀ i, l1 !! i ≡{n}≡ l2 !! i.
  Abort.

  (* analogous test for [Equiv] and https://github.com/rocq-prover/rocq/issues/14441.
  From https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/700#note_69303. *)
  Lemma list_equiv_lookup_ofe {A : ofe} (l1 l2 : list A) :
    l1 ≡ l2 ↔ ∀ i, l1 !! i ≡ l2 !! i.
  Abort.
End test_dist_equiv_mode.

(** Make sure that the same [Equivalence] instance is picked for Leibniz OFEs
with carriers that are definitionally equal. See also
https://gitlab.mpi-sws.org/iris/iris/issues/299 *)
Definition tag := nat.
Canonical Structure tagO := leibnizO tag.
Goal tagO = natO.
Proof. reflexivity. Qed.

Global Instance test_cofe {Σ} : Cofe (iPrePropO Σ) := _.

(** Make sure that the instance [leibnizO_leibniz] is fired (and does not suffer
from unification issues. *)
Goal LeibnizEquiv natO.
Proof. apply _. Qed.
Goal LeibnizEquiv nat.
Proof. apply _. Qed.
Goal LeibnizEquiv tagO.
Proof. apply _. Qed.
Goal LeibnizEquiv tag.
Proof. apply _. Qed.

Section tests.
  Context `{!invGS_gen hlc Σ}.

  Program Definition test : (iPropO Σ -n> iPropO Σ) -n> (iPropO Σ -n> iPropO Σ) :=
    λne P v, (▷ (P v))%I.
  Solve Obligations with solve_proper.

End tests.

(** Regression test for <https://gitlab.mpi-sws.org/iris/iris/issues/255>. *)
Definition testR := authR (prodUR
        (prodUR
          (optionUR (exclR unitO))
          (optionUR (exclR unitO)))
        (optionUR (agreeR (boolO)))).
Section test_prod.
  Context `{!inG Σ testR}.
  Lemma test_prod_persistent γ :
    Persistent (PROP:=iPropI Σ) (own γ (◯((None, None), Some (to_agree true)))).
  Proof. apply _. Qed.
End test_prod.

(** Make sure the [auth]/[gmap_view] notation does not mix up its arguments. *)
Definition auth_check {A : ucmra} :
  auth A = authO A := eq_refl.
Definition gmap_view_check {K : Type} `{Countable K} {V : cmra} :
  gmap_view K V = gmap_viewO K V := eq_refl.

Lemma uncurry_ne_test {A B C : ofe} (f : A → B → C) :
  NonExpansive2 f → NonExpansive (uncurry f).
Proof. apply _. Qed.
Lemma uncurry3_ne_test {A B C D : ofe} (f : A → B → C → D) :
  NonExpansive3 f → NonExpansive (uncurry3 f).
Proof. apply _. Qed.
Lemma uncurry4_ne_test {A B C D E : ofe} (f : A → B → C → D → E) :
  NonExpansive4 f → NonExpansive (uncurry4 f).
Proof. apply _. Qed.

Lemma curry_ne_test {A B C : ofe} (f : A * B → C) :
  NonExpansive f → NonExpansive2 (curry f).
Proof. apply _. Qed.
Lemma curry3_ne_test {A B C D : ofe} (f : A * B * C → D) :
  NonExpansive f → NonExpansive3 (curry3 f).
Proof. apply _. Qed.
Lemma curry4_ne_test {A B C D E : ofe} (f : A * B * C * D → E) :
  NonExpansive f → NonExpansive4 (curry4 f).
Proof. apply _. Qed.

(** Regression test for https://gitlab.mpi-sws.org/iris/iris/-/issues/577 *)
Lemma list_bind_ne_test {A B : ofe} (f : A → list B) :
  NonExpansive f → NonExpansive (mbind f : list A → list B).
Proof. apply _. Qed.

(** Needs "new" unification for [Monoid] *)
Definition big_op_test (l : list Qp) : option Qp :=
  [^op list] x ∈ l, Some x.

(** [frac] and [ufrac] are different cameras on the same carrier (namely [Qp]).
They have the same operator (namely, addition on [Qp]), but different validity
predicates ([≤ 1] and [True], respectively). The big operators only rely on
the "monoid" part of [frac] and [ufrac] (i.e., not their validity), so it should
not matter via which camera we obtained the [Monoid] instance. We test that the
difference in [Monoid] instance (which is not even visible, unless one enables
printing of implicit arguments) does not affect definitional equality of big
operators. *)
Lemma big_opL_should_be_eq l :
  ([^op list] x ∈ (l : list (option frac)), x) =
  ([^op list] x ∈ (l : list (option ufrac)), x).
Proof. reflexivity. Qed.

Lemma big_opM_should_be_eq `{Countable K} m :
  ([^op map] x ∈ (m : gmap K (option frac)), x) =
  ([^op map] x ∈ (m : gmap K (option ufrac)), x).
Proof. reflexivity. Qed.

Lemma big_opS_should_be_eq X :
  ([^op set] x ∈ (X : gset (option frac)), x) =
  ([^op set] x ∈ (X : gset (option ufrac)), x).
Proof. reflexivity. Qed.

Lemma big_opMS_should_be_eq `{Countable K} X :
  ([^op mset] x ∈ (X : gmultiset (option frac)), x) =
  ([^op mset] x ∈ (X : gmultiset (option ufrac)), x).
Proof. reflexivity. Qed.
