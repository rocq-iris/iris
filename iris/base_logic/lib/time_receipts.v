(** This file implements time receipts, a resource to track permissions to
eliminate multiple laters around each (program) step. As for later credits,
there is only a single instance of the time receipt ghost state. This file
defines the time receipt resources and corresponding supply [time_receipt_supply].

There are 2 types of time receipts:

- Persistent time receipts [⧖□ n] which represent a lower bound on the number of
  laters that can be eliminated each step, and the remaining number of later
  credits generated _during_ each (program) step. 
- Exclusive time receipts [⧖+ n] which represent permissions to generate later
  credits _around_ each (program) step.

Exclusive time receipts can be converted into persistent ones by either:

- Adding them to an existing persistent time receipt using [time_receipt_pers_incr].
- Creating a persistent copy for the same amount using [time_receipt_excl_pers_get].

The [time_receipt_supply] should not usually be used directly, it is used in the
internal model of the physical step modality which models the elimination of
laters and generation of later credits using time receipts. (FUTURE WORK). *)
From iris.prelude Require Import options.
From iris.algebra.lib Require Import time_receipts.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.

(** The ghost state for time receipts  *)
Class time_receiptGpreS (Σ : gFunctors) := TimeReceiptGpreS {
  #[local] time_receiptGpreS_inG :: inG Σ time_receiptUR;
}.

Class time_receiptGS (Σ : gFunctors) := TimeReceiptGS {
  #[local] time_receiptGS_inG :: inG Σ time_receiptUR;
  time_receiptGS_name : gname;
}.
Global Hint Mode time_receiptGS - : typeclass_instances.

Definition time_receiptΣ := #[GFunctor time_receiptUR].
Global Instance subG_time_receiptΣ {Σ} :
  subG time_receiptΣ Σ → time_receiptGpreS Σ.
Proof. solve_inG. Qed.

(** Exclusive (Additive) time receipts. *)
Local Definition time_receipt_excl_def `{!time_receiptGS Σ} (n : nat) : iProp Σ :=
  own time_receiptGS_name (time_receipt_frag_excl n).
Local Definition time_receipt_excl_aux : seal (@time_receipt_excl_def).
Proof. by eexists. Qed.
Definition time_receipt_excl := time_receipt_excl_aux.(unseal).
Local Definition time_receipt_excl_eq :
  @time_receipt_excl = @time_receipt_excl_def := time_receipt_excl_aux.(seal_eq).
Global Arguments time_receipt_excl {_ _}.

(** Persistent time receipts. *)
Local Definition time_receipt_pers_def `{!time_receiptGS Σ} (n : nat) : iProp Σ :=
  own time_receiptGS_name (time_receipt_frag_pers n).
Local Definition time_receipt_pers_aux : seal (@time_receipt_pers_def).
Proof. by eexists. Qed.
Definition time_receipt_pers := time_receipt_pers_aux.(unseal).
Local Definition time_receipt_pers_eq :
  @time_receipt_pers = @time_receipt_pers_def := time_receipt_pers_aux.(seal_eq).
Global Arguments time_receipt_pers {_ _}.

Notation "'⧖+'  n" := (time_receipt_excl n) (at level 1).
Notation "'⧖□'  n" := (time_receipt_pers n) (at level 1).

Local Definition time_receipt_supply_def `{!time_receiptGS Σ} (m : nat) : iProp Σ :=
  own time_receiptGS_name (time_receipt_auth m).
Local Definition time_receipt_supply_aux : seal (@time_receipt_supply_def).
Proof. by eexists. Qed.
Definition time_receipt_supply := time_receipt_supply_aux.(unseal).
Local Definition time_receipt_supply_eq :
  @time_receipt_supply = @time_receipt_supply_def := time_receipt_supply_aux.(seal_eq).
Global Arguments time_receipt_supply {Σ _} m.

Local Ltac unseal := rewrite
  ?time_receipt_excl_eq /time_receipt_excl_def
  ?time_receipt_pers_eq /time_receipt_pers_def
  ?time_receipt_supply_eq /time_receipt_supply_def.

Section time_receipts.
  Context `{!time_receiptGS Σ}.
  Implicit Types n m : nat.

  Global Instance time_receipt_excl_timeless n : Timeless (⧖+ n).
  Proof. unseal. apply _. Qed.
  Global Instance time_receipt_excl_0_persistent : Persistent (⧖+ 0).
  Proof. unseal. apply _. Qed.
  Global Instance time_receipt_pers_timeless n : Timeless (⧖□ n).
  Proof. unseal. apply _. Qed.
  Global Instance time_receipt_pers_persistent n : Persistent (⧖□ n).
  Proof. unseal. apply _. Qed.

  Lemma time_receipt_excl_split n1 n2 :
    ⧖+ (n1 + n2) ⊣⊢ ⧖+ n1 ∗ ⧖+ n2.
  Proof. unseal. rewrite -own_op //=. Qed.

  Lemma time_receipt_pers_split n1 n2 :
    ⧖□ (n1 `max` n2) ⊣⊢ ⧖□ n1 ∗ ⧖□ n2.
  Proof. unseal. rewrite -own_op //=. Qed.

  Lemma time_receipt_excl_zero : ⊢ |==> ⧖+ 0.
  Proof. unseal. iApply own_unit. Qed.

  Lemma time_receipt_pers_zero : ⊢ |==> ⧖□ 0.
  Proof. unseal. iApply own_unit. Qed.

  Lemma time_receipt_excl_weaken {n1} n2 :
    n2 ≤ n1 → ⧖+ n1 -∗ ⧖+ n2.
  Proof.
    intros [k ->]%Nat.le_sum.
    rewrite time_receipt_excl_split.
    iIntros "[$ _]".
  Qed.

  Lemma time_receipt_pers_weaken {n1} n2 :
    n2 ≤ n1 → ⧖□ n1 -∗ ⧖□ n2.
  Proof.
    intros.
    rewrite -(max_r n2 n1) // time_receipt_pers_split.
    iIntros "[$ _]".
  Qed.

  Lemma time_receipt_excl_succ n :
    ⧖+ (S n) ⊣⊢ ⧖+ 1 ∗ ⧖+ n.
  Proof. rewrite -time_receipt_excl_split //=. Qed.
  
  Lemma time_receipt_pers_incr n1 n2 :
    ⧖+ n1 -∗ ⧖□ n2 ==∗ ⧖□ (n1 + n2).
  Proof.
    unseal. iIntros "Htr Htrp".
    iMod (own_update_2 with "Htr Htrp") as "$"; [|done].
    apply time_receipt_frag_excl_persist.
  Qed.

  Lemma time_receipt_excl_pers_get n :
    ⧖+ n ==∗ ⧖+ n ∗ ⧖□ n.
  Proof.
    unseal. iIntros "Htr".
    iMod(own_update with "Htr") as "[$ $]"; [|done].
    apply time_receipt_frag_excl_get_pers.
  Qed.

  Lemma time_receipt_supply_pers_bound n m :
    time_receipt_supply m -∗ ⧖□ n -∗ ⌜n ≤ m⌝.
  Proof.
    unseal. iIntros "Hauth Htrp".
    iCombine "Hauth Htrp" gives %Hop.
    by apply time_receipt_frag_pers_valid in Hop.
  Qed.

  Lemma time_receipt_supply_bound_both n1 n2 m :
    time_receipt_supply m -∗ ⧖+ n1 -∗ ⧖□ n2 -∗ ⌜n1 + n2 ≤ m⌝.
  Proof.
    iIntros "Hauth Htr Htrp".
    iMod (time_receipt_pers_incr with "Htr Htrp") as "Htrp".
    iApply (time_receipt_supply_pers_bound with "Hauth Htrp").
  Qed.

  (** This lemma increments the supply, incrementing both the exclusive and
  persistent partitions by the same amount [k]. This ensures the persistent
  partition remains at least as large as the exclusive partition, which is
  necessary for the [time_receipt_excl_pers_get] rule above.
  As the exact size of the persistent partition is unknown, the lemma increments
  a lower bound [⧖□ n]. This is not necessary for exclusive time receipts, as
  the resulting exclusive time receipt [⧖+ k] can be added to any existing
  exclusive time receipt [⧖+ n'] afterwards to give [⧖+ (n' + k)]. *)
  Lemma time_receipt_supply_incr k m n :
    time_receipt_supply m -∗ ⧖□ n ==∗
    time_receipt_supply (m + k + k) ∗ ⧖+ k ∗ ⧖□ (n + k).
  Proof.
    unseal. iIntros "Hauth Htrp".
    iMod (own_update_2 with "Hauth Htrp") as "[[$ Hauth'] Htrp']".
    { apply time_receipt_auth_incr. }
    by iFrame.
  Qed.

  (** The rule for [+] has lower cost than the one for [S], otherwise Rocq's
  unification applies the [S] hint too eagerly. See Iris issue #470.
  These instances correspond to those for later credits. *)
  Global Instance from_sep_time_receipt_excl_add n1 n2 :
    FromSep (⧖+ (n1 + n2)) (⧖+ n1) (⧖+ n2) | 0.
  Proof. by rewrite /FromSep time_receipt_excl_split. Qed.
  Global Instance from_sep_time_receipt_excl_S n :
    FromSep (⧖+ (S n)) (⧖+ 1) (⧖+ n) | 1.
  Proof. by rewrite /FromSep (time_receipt_excl_succ n). Qed.

   (** When combining time receipts with [iCombine], the priorities are
  reversed when compared to [FromSep] and [IntoSep]. This causes
  [⧖+ n] and [⧖+ 1] to be combined as [⧖+ (S n)], not as [⧖+ (n + 1)].
  These instances correspond to those those for later credits. *)
  Global Instance combine_sep_time_receipt_excl_add n1 n2 :
    CombineSepAs (⧖+ n1) (⧖+ n2) (⧖+ (n1 + n2)) | 1.
  Proof. by rewrite /CombineSepAs time_receipt_excl_split. Qed.
  Global Instance combine_sep_time_receipt_excl_S_l n :
    CombineSepAs (⧖+ n) (⧖+ 1) (⧖+ (S n)) | 0.
  Proof. by rewrite /CombineSepAs comm (time_receipt_excl_succ n). Qed.

  Global Instance into_sep_time_receipt_excl_add n1 n2 :
    IntoSep (⧖+ (n1 + n2)) (⧖+ n1) (⧖+ n2) | 0.
  Proof. by rewrite /IntoSep time_receipt_excl_split. Qed.
  Global Instance into_sep_time_receipt_excl_S n :
    IntoSep (⧖+ (S n)) (⧖+ 1) (⧖+ n) | 1.
  Proof. by rewrite /IntoSep (time_receipt_excl_succ n). Qed.

  Global Instance combine_sep_time_receipt_pers_max n1 n2 :
    CombineSepAs (⧖□ n1) (⧖□ n2) (⧖□ (n1 `max` n2)) | 1.
  Proof. by rewrite /CombineSepAs time_receipt_pers_split. Qed.
End time_receipts.

Lemma time_receipt_supply_alloc `{!time_receiptGpreS Σ} n :
  ⊢ |==> ∃ _ : time_receiptGS Σ, time_receipt_supply (n + n) ∗ ⧖+ n.
Proof.
  unseal.
  iMod (own_alloc (time_receipt_auth (n + n) ⋅ time_receipt_frag_excl n))
    as (γTR) "[Hauth Htr]"; first (by apply time_receipt_frag_excl_valid).
  iExists (TimeReceiptGS _ _ γTR). by iFrame.
Qed.
