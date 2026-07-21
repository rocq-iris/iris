(** This is just an integration file for [iris_staging.algebra.list];
both should be stabilized together. *)
From iris.algebra Require Import cmra.
From iris.unstable.algebra Require Import list.
From iris.bi Require Import algebra.

Section algebra.
  Context `{!Sbi PROP}.

  (* Force implicit argument [PROP] *)
  Notation "P ⊢ Q" := (bi_entails (PROP:=PROP) P Q).
  Notation "P ⊣⊢ Q" := (equiv (A:=PROP) P%I Q%I).

  Section list_cmra.
    Context {A : ucmra}.
    Implicit Types l : list A.

    Lemma list_validI l : ✓ l ⊣⊢ ∀ i, ✓ (l !! i).
    Proof. sbi_unfold=> n. apply list_lookup_validN. Qed.
  End list_cmra.
End algebra.
