(** RA for time receipts with disjoint exclusive and persistent lower bounds.

The authoritative is a single [nat] representing the total time receipts,
which is split into additive and persistent partitions, where the persistent
partition is at least as large as the additive partition.
The exact partitioning is not fixed by the authoritative element.

There are two kinds of fragment: an exclusive (additive) lower bound
[time_receipt_frag_excl] and persistent lower bound
[time_receipt_frag_pers] of the additive and persistent partitions
respectively.

The key properties of the resource algebra are that:
1. Without requiring the authoritative, presistent fragments can be derived from
   additive ones in a snapshot operation [time_receipt_frag_excl_get_pers].
2. Without the authoritative, additive fragments [time_receipt_frag_excl_persist]
   can be used to shrink the additive and expand the persistent partition.
3. Increasing the authoritative expands both partitions by the same amount,
   generating new additive fragments [time_receipt_frag_excl] and incrementing
   any persistent fragments [time_receipt_frag_pers].
   
This RA is used to implement time receipts, which are permissions to eliminate
laters around (program) steps. Instead of using this RA directly, one would
generally use the time receipts in [iris.base_logic.lib.time_receipts] and the
physical step modality (TODO) to generate and use time receipts. *)
From iris.prelude Require Import options.
From iris.algebra Require Export view numbers proofmode_classes.

Local Definition time_receipt_view_fragUR {SI : sidx} := prodUR natUR max_natUR.

Section rel.
  Context {SI : sidx}.
  Implicit Types (a : nat) (f : nat * max_nat).

  (** The authoritative [a] is partitioned into an additive [a1] and a persistent
  [a2] part for which the respective fragments ([f.1] and [f.2]) are lower bounds,
  respectively. *)
  Local Definition time_receipt_view_rel_raw (n : SI) a f : Prop :=
    ∃ a1 a2, a = a1 + a2 ∧ a1 ≤ a2 ∧ f.1 ≤ a1 ∧ max_nat_car f.2 ≤ a2.

  Local Lemma time_receipt_view_rel_raw_mono n1 n2 a1 a2 f1 f2:
    time_receipt_view_rel_raw n1 a1 f1 →
    a1 ≡{n2}≡ a2 →
    f2 ≼{n2} f1 →
    (n2 ≤ n1)%sidx →
    time_receipt_view_rel_raw n2 a2 f2.
  Proof.
    intros (a21 & a22 & H) Haeq Hble Hnle.
    exists a21, a22.
    destruct f1 as [f11 f12], f2 as [f21 f22].
    rewrite pair_includedN -!cmra_discrete_included_iff nat_included
      max_nat_included /= in Hble.
    rewrite -discrete_iff in Haeq. simplify_eq/=. lia.
  Qed.

  Local Lemma time_receipt_view_rel_raw_valid n a f :
    time_receipt_view_rel_raw n a f → ✓{n} f.
  Proof. done. Qed.

  Local Lemma time_receipt_view_rel_raw_unit n :
    ∃ a, time_receipt_view_rel_raw n a ε.
  Proof. by exists 0, 0, 0. Qed.

  Global Canonical Structure time_receipt_view_rel :
      view_rel natUR time_receipt_view_fragUR :=
    ViewRel time_receipt_view_rel_raw time_receipt_view_rel_raw_mono
            time_receipt_view_rel_raw_valid time_receipt_view_rel_raw_unit.

  Local Lemma time_receipt_view_rel_exists n f :
    (∃ a, time_receipt_view_rel n a f) ↔ ✓{n} f.
  Proof.
    split.
    { intros [a Hrel]. eapply time_receipt_view_rel_raw_valid, Hrel. }
    intros Hf. destruct f as [f1 [f2]].
    exists (f1 + f1 `max` f2), f1, (f1 `max` f2). simpl. lia.
  Qed.

  Local Lemma time_receipt_view_rel_unit n a : time_receipt_view_rel n a ε ↔ ✓{n} a.
  Proof.
    split; first done.
    intros. exists 0, a. rewrite (_ : ε = (0, MaxNat 0)) //=. lia.
  Qed.

  Global Instance time_receipt_view_rel_discrete :
    ViewRelDiscrete time_receipt_view_rel.
  Proof. by intros n a f. Qed.
End rel.

(** Allows us to use [simpl] in the proofs below instead of having to [unfold]. *)
Local Arguments time_receipt_view_rel_raw _ _ _ !_ /.

Definition time_receipt {SI : sidx} := view time_receipt_view_rel_raw.
Definition time_receiptO {SI : sidx} := viewO time_receipt_view_rel.
Definition time_receiptR {SI : sidx} := viewR time_receipt_view_rel.
Definition time_receiptUR {SI : sidx} := viewUR time_receipt_view_rel.

Definition time_receipt_auth {SI : sidx} (m : nat) : time_receipt := ●V m.
Definition time_receipt_frag_excl {SI : sidx} (n : nat) : time_receipt :=
  ◯V (n, MaxNat 0).
Definition time_receipt_frag_pers {SI : sidx} (n : nat) : time_receipt :=
  ◯V (0, MaxNat n).

Global Typeclasses Opaque time_receipt_auth time_receipt_frag_excl
  time_receipt_frag_pers.

Section time_receipt.
  Context {SI : sidx}.
  Implicit Types n m : nat.

  Global Instance time_receipt_frag_pers_core_id n :
    CoreId (time_receipt_frag_pers n).
  Proof. by constructor. Qed.

  Global Instance time_receipt_frag_excl_0_core_id :
    CoreId (time_receipt_frag_excl 0).
  Proof. by constructor. Qed.

  Lemma time_receipt_frag_excl_op n1 n2 :
    time_receipt_frag_excl (n1 + n2) =
    time_receipt_frag_excl n1 ⋅ time_receipt_frag_excl n2.
  Proof. done. Qed.

  Lemma time_receipt_frag_pers_op n1 n2 :
    time_receipt_frag_pers (n1 `max` n2) =
    time_receipt_frag_pers n1 ⋅ time_receipt_frag_pers n2.
  Proof. done. Qed.

  Global Instance time_receipt_frag_excl_is_op n n1 n2 :
    IsOp n n1 n2 →
    IsOp' (time_receipt_frag_excl n) (time_receipt_frag_excl n1)
          (time_receipt_frag_excl n2).
  Proof. done. Qed.

  Global Instance time_receipt_frag_pers_is_op n n1 n2 :
    IsOp (MaxNat n) (MaxNat n1) (MaxNat n2) →
    IsOp' (time_receipt_frag_pers n) (time_receipt_frag_pers n1)
          (time_receipt_frag_pers n2).
  Proof. done. Qed.

  Lemma time_receipt_frag_excl_valid m n :
    ✓ (time_receipt_auth m ⋅ time_receipt_frag_excl n) ↔ n + n ≤ m.
  Proof.
    rewrite view_both_valid /=. split.
    - intros Hrel. specialize (Hrel 0ᵢ) as (a & b & ?); lia.
    - intros ? _. exists n, (m - n). lia.
  Qed.

  Lemma time_receipt_frag_pers_valid m n :
    ✓ (time_receipt_auth m ⋅ time_receipt_frag_pers n) ↔ n ≤ m.
  Proof.
    rewrite view_both_valid /=. split.
    - intros Hrel. specialize (Hrel 0ᵢ) as (a & b & ?); lia.
    - intros ? _. exists 0, m. lia.
  Qed.

  Lemma time_receipt_view_frag_both_valid m n1 n2 :
    ✓ (time_receipt_auth m ⋅
        (time_receipt_frag_excl n1 ⋅ time_receipt_frag_pers n2)) →
    n1 + n2 ≤ m.
  Proof.
    rewrite view_both_valid /= nat_op.
    intros Hrel. specialize (Hrel 0ᵢ) as (a & f & -> & Haf). lia.
  Qed.

  Lemma time_receipt_frag_excl_persist n1 n2 :
    time_receipt_frag_excl n1 ⋅ time_receipt_frag_pers n2 ~~>
      time_receipt_frag_pers (n1 + n2).
  Proof.
    rewrite -view_frag_op /=.
    apply view_update_frag=> a d ?. rewrite /= !nat_op.
    intros (a1 & a2 & -> & ? & ? & ?). exists (a1 - n1), (a2 + n1). lia.
  Qed.

  Lemma time_receipt_frag_excl_get_pers n:
    time_receipt_frag_excl n ~~>
      time_receipt_frag_excl n ⋅ time_receipt_frag_pers n.
  Proof.
    apply view_update_frag=> a d ?. rewrite /= !nat_op.
    intros (a1 & a2 & -> & ? & ? & ?). exists a1, a2; lia.
  Qed.

  (** This lemma increments the authoritative by incrementing both the exclusive
  and persistent partitions by the same amounts ensuring that the persistent partition
  remains at least as large as the exclusive partition after the update.
  The lemma takes a persistent time receipt fragment as witness to be increased, but not
  an exclusive fragment as the resulting exclusive fragment can be added to any existing
  exclusive fragment. *)
  Lemma time_receipt_auth_incr m n k:
    time_receipt_auth m ⋅ time_receipt_frag_pers n ~~>
      time_receipt_auth (m + k + k) ⋅
      time_receipt_frag_pers (n + k) ⋅
      time_receipt_frag_excl k.
  Proof.
    rewrite -assoc. apply view_update=> a ?. rewrite /= !nat_op.
    intros (a1 & a2 & -> & ? & ? & ?). exists (a1 + k), (a2 + k). lia.
  Qed.
End time_receipt.
