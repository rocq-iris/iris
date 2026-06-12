From iris.algebra Require Import monoid.
From iris.bi Require Export interface.

Definition bi_iff {SI : sidx} {PROP : bi} (P Q : PROP) : PROP :=
  (P → Q) ∧ (Q → P).
Global Arguments bi_iff {SI _} _%_I _%_I : simpl never.
Global Instance: Params (@bi_iff) 2 := {}.
Infix "↔" := bi_iff : bi_scope.

Definition bi_wand_iff {SI : sidx} {PROP : bi} (P Q : PROP) : PROP :=
  (P -∗ Q) ∧ (Q -∗ P).
Global Arguments bi_wand_iff {SI _} _%_I _%_I : simpl never.
Global Instance: Params (@bi_wand_iff) 2 := {}.
Infix "∗-∗" := bi_wand_iff : bi_scope.
Notation "P ∗-∗ Q" := (⊢ P ∗-∗ Q) : stdpp_scope.

Class Persistent {SI : sidx} {PROP : bi} (P : PROP) :=
  persistent : P ⊢ <pers> P.
Global Arguments Persistent {SI _} _%_I : simpl never.
Global Arguments persistent {SI _} _%_I {_}.
Global Hint Mode Persistent - + ! : typeclass_instances.
Global Instance: Params (@Persistent) 2 := {}.
Global Hint Extern 100 (Persistent (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

Definition bi_affinely {SI : sidx} {PROP : bi} (P : PROP) : PROP := emp ∧ P.
Global Arguments bi_affinely {SI _} _%_I : simpl never.
Global Instance: Params (@bi_affinely) 2 := {}.
Global Typeclasses Opaque bi_affinely.
Notation "'<affine>' P" := (bi_affinely P) : bi_scope.

Class Affine {SI : sidx} {PROP : bi} (Q : PROP) := affine : Q ⊢ emp.
Global Arguments Affine {SI _} _%_I : simpl never.
Global Arguments affine {SI _} _%_I {_}.
Global Hint Mode Affine - + ! : typeclass_instances.
Global Hint Extern 100 (Affine (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

Definition bi_absorbingly {SI : sidx} {PROP : bi} (P : PROP) : PROP := True ∗ P.
Global Arguments bi_absorbingly {SI _} _%_I : simpl never.
Global Instance: Params (@bi_absorbingly) 2 := {}.
Global Typeclasses Opaque bi_absorbingly.
Notation "'<absorb>' P" := (bi_absorbingly P) : bi_scope.

Class Absorbing {SI : sidx} {PROP : bi} (P : PROP) := absorbing : <absorb> P ⊢ P.
Global Arguments Absorbing {SI _} _%_I : simpl never.
Global Arguments absorbing {SI _} _%_I.
Global Hint Mode Absorbing - + ! : typeclass_instances.
Global Hint Extern 100 (Absorbing (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

Definition bi_persistently_if {SI : sidx} {PROP : bi}
    (p : bool) (P : PROP) : PROP :=
  (if p then <pers> P else P)%I.
Global Arguments bi_persistently_if {SI _} !_ _%_I /.
Global Instance: Params (@bi_persistently_if) 3 := {}.
Global Typeclasses Opaque bi_persistently_if.
Notation "'<pers>?' p P" := (bi_persistently_if p P) : bi_scope.

Definition bi_affinely_if {SI : sidx} {PROP : bi}
    (p : bool) (P : PROP) : PROP :=
  (if p then <affine> P else P)%I.
Global Arguments bi_affinely_if {SI _} !_ _%_I /.
Global Instance: Params (@bi_affinely_if) 3 := {}.
Global Typeclasses Opaque bi_affinely_if.
Notation "'<affine>?' p P" := (bi_affinely_if p P) : bi_scope.

Definition bi_absorbingly_if {SI : sidx} {PROP : bi}
    (p : bool) (P : PROP) : PROP :=
  (if p then <absorb> P else P)%I.
Global Arguments bi_absorbingly_if {SI _} !_ _%_I /.
Global Instance: Params (@bi_absorbingly_if) 3 := {}.
Global Typeclasses Opaque bi_absorbingly_if.
Notation "'<absorb>?' p P" := (bi_absorbingly_if p P) : bi_scope.

Definition bi_intuitionistically {SI : sidx} {PROP : bi} (P : PROP) : PROP :=
  (<affine> <pers> P)%I.
Global Arguments bi_intuitionistically {SI _} _%_I : simpl never.
Global Instance: Params (@bi_intuitionistically) 2 := {}.
Global Typeclasses Opaque bi_intuitionistically.
Notation "□ P" := (bi_intuitionistically P) : bi_scope.

Definition bi_intuitionistically_if {SI : sidx} {PROP : bi}
    (p : bool) (P : PROP) : PROP :=
  (if p then □ P else P)%I.
Global Arguments bi_intuitionistically_if {SI _} !_ _%_I /.
Global Instance: Params (@bi_intuitionistically_if) 3 := {}.
Global Typeclasses Opaque bi_intuitionistically_if.
Notation "'□?' p P" := (bi_intuitionistically_if p P) : bi_scope.

Fixpoint bi_laterN {SI : sidx} {PROP : bi} (n : nat) (P : PROP) : PROP :=
  match n with
  | O => P
  | S n' => ▷ ▷^n' P
  end
where "▷^ n P" := (bi_laterN n P) : bi_scope.
Global Arguments bi_laterN {SI _} !_%_nat_scope _%_I.
Global Instance: Params (@bi_laterN) 3 := {}.
Notation "▷? p P" := (bi_laterN (Nat.b2n p) P) : bi_scope.

(** The "except-0" modality [◇ P] says that we are either at step-index 0 or [P]
holds, i.e., it holds at all step indices except 0. In the step-indexed model,
the definition expands to [(◇ P) n] iff [n = 0 ∨ P n] for [P : nat → Prop]. *)
Definition bi_except_0 {SI : sidx} {PROP : bi} (P : PROP) : PROP := ▷ False ∨ P.
Global Arguments bi_except_0 {SI _} _%_I : simpl never.
Notation "◇ P" := (bi_except_0 P) : bi_scope.
Global Instance: Params (@bi_except_0) 2 := {}.
Global Typeclasses Opaque bi_except_0.

(** The "only-0" modality [<only0> P] says that [P] holds at step-index 0. In the
step-indexed model, the definition expands to [(<only0> P) n] iff [P 0] for
[P : nat → Prop]. (If you unfold the definition of [(<only0> P) n] directly into the
model, you get [∀ n' ≤ n, n' = 0 → P n'], which is equivalent to [P 0].) *)
Definition bi_only_0 {SI : sidx} {PROP : bi} (P : PROP) : PROP := ▷ False → P.
Global Typeclasses Opaque bi_only_0.
Global Instance: Params (@bi_only_0) 2 := {}.
Notation "<only0> P" := (bi_only_0 P)
  (at level 20, right associativity) : bi_scope.

(* Timeless propositions are propositions that do not depend on the step-index.
   There are two equivalent ways of expressing that a step-indexed proposition
   [P : nat → Prop] is timeless:
   * Option one, used here, says that [∀ n, P n → P (S n)]. In the logic, this
     is stated as [▷ P ⊢ ◇ P] (which actually reads [∀ n > 0, P (n-1) → P n],
     but this is trivially equivalent).
   * Option two says that [∀ n, P 0 → P n]. In the logic, this is stated as a
     [<only0> P ⊢ P]. The [▷ False] in the definition of [<only0>] expresses that we
     can only obtain [P] at step-index is 0.

   Both formulations are equivalent. In the logic, this can be shown using Löb
   induction and [later_false_em]. In the model, this follows from regular
   natural induction.
   The law [timeless_alt] in [derived_laws_later.v] provides option two, by
   proving that both versions are equivalent in the logic.  *)
Class Timeless {SI : sidx} {PROP : bi} (P : PROP) := timeless : ▷ P ⊢ ◇ P.
Global Arguments Timeless {SI _} _%_I : simpl never.
Global Arguments timeless {SI _} _%_I {_}.
Global Hint Mode Timeless - + ! : typeclass_instances.
Global Instance: Params (@Timeless) 2 := {}.
Global Hint Extern 100 (Timeless (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

(** An optional precondition [mP] to [Q].
    TODO: We may actually consider generalizing this to a list of preconditions,
    and e.g. also using it for texan triples. *)
Definition bi_wandM {SI : sidx} {PROP : bi}
    (mP : option PROP) (Q : PROP) : PROP :=
  match mP with
  | None => Q
  | Some P => P -∗ Q
  end.
Global Arguments bi_wandM {SI _} !_%_I _%_I /.
Notation "mP -∗? Q" := (bi_wandM mP Q)
  (at level 99, Q at level 200, right associativity) : bi_scope.
