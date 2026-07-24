From stdpp Require Import strings.
From iris.si_logic Require Import bi.
From iris.proofmode Require Import proofmode.
Unset Mangle Names.

Check "unseal_test".
Lemma unseal_test {SI : sidx} (P Q : siProp) (Φ : nat → siProp) :
  P ∧ ▷ Q ∧ (∃ x, Φ x) ⊣⊢ ∃ x, P ∗ ▷ Q ∧ emp ∨ Φ x.
Proof.
  siProp.unseal.
  Show.
Abort.

(** Make sure that [siProp]s are parsed in [bi_scope]. *)
Definition test {SI : sidx} : siProp := ▷ True.
Definition testI {SI : sidx} : siPropI := ▷ True.

Check "test_persistently_exist".
Lemma test_persistently_exist {A} (Φ : A → siProp) :
  (∃ x, Φ x) -∗ True.
Proof.
  iIntros "#H".
  (* Since [siProp] satisfies [BiPersistentlyExist], the hypothesis [H] should
  remain in the persistent context. *)
  iDestruct "H" as (x) "H".
  Show.
Abort.
