From stdpp Require Import propset gmap strings.
From iris Require Import algebra.mra.

Unset Mangle Names.

Abbreviation gset_mra K:= (mra (⊆@{gset K})).

(* Check if we indeed get [=], i.e., the right [Inj] instance is used. *)
Check "mra_test_eq".
Lemma mra_test_eq {SI : sidx} X Y :
  to_mra X ≡@{gset_mra nat} to_mra Y → X = Y.
Proof. intros ?%(inj _). Show. done. Qed.

Abbreviation propset_mra K := (mra (⊆@{propset K})).

Lemma mra_test_equiv {SI : sidx} X Y :
  to_mra X ≡@{propset_mra nat} to_mra Y → X ≡ Y.
Proof. intros ?%(inj _). done. Qed.
