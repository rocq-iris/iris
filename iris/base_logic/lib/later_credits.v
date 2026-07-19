(** This file implements later credits, in particular the later-elimination update.
That update is used internally to define the Iris [fupd]; it should not
usually be directly used unless you are defining your own [fupd]. *)
From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Export auth numbers.
From iris.base_logic.lib Require Import iprop own.
Import uPred.

(** The [hlc : has_lc] parameter indicates whether later credits are enabled
or not. From a user's point of view there are two differences:

- If later credits are enabled ([hlc = HasLc]), we obtain the rule
  [lc_le_upd_elim_later : £ 1 -∗ (▷ P) -∗ |==£> P], which allows us strip a
  later by spending a credit. This rule is used to prove the similar rule for
  the fancy update modality.
- If later credits are disabled ([hlc = HasNoLc]), we obtain the rule
  [le_upd_keep : (|==£|■> P) ∧ (P -∗ |==£> Q) ⊢ |==£> Q] without the
  side-condition that [P] should be timeless (the "finally" modality [|==£|■>]
  is described further below in this file). This rule is used to derive the
  plain interaction rules [BiFUpdSbi] of the fancy update modality.

In the model, if later credits are disabled ([hlc = HasNoLc]), we simply define
the credit [£ n] as [True] and the supply [lc_supply n] as [n = 0]. This choice
gives uniform proofs, where we do not have to case split on [hlc] for nearly all
rules. *)

Inductive has_lc := HasLc | HasNoLc.

(** The ghost state for later credits *)
Class lcGpreS (Σ : gFunctors) := LcGpreS {
  #[local] lcGpreS_inG :: inG Σ (authR natUR)
}.

Class lcGS (hlc : has_lc) (Σ : gFunctors) := LcGS {
  #[local] lcGS_inG :: inG Σ (authR natUR);
  lcGS_name : gname;
}.
Global Hint Mode lcGS - - : typeclass_instances.

Definition lcΣ := #[GFunctor (authR (natUR))].
Global Instance subG_lcΣ {Σ} : subG lcΣ Σ → lcGpreS Σ.
Proof. solve_inG. Qed.

(** The user-facing credit resource, denoting ownership of [n] credits
(but only if later credits are enabled). *)
Local Definition lc_def `{!lcGS hlc Σ} (n : nat) : iProp Σ :=
  if hlc is HasLc then own lcGS_name (◯ n) else True.
Local Definition lc_aux : seal (@lc_def). Proof. by eexists. Qed.
Definition lc := lc_aux.(unseal).
Local Definition lc_unseal : @lc = @lc_def := lc_aux.(seal_eq).
Global Arguments lc {hlc Σ _} n.

Notation "'£'  n" := (lc n) (at level 1).

(** The internal authoritative part of the credit ghost state, tracking how many
credits are available in total. Users should not directly interface with this. *)
Local Definition lc_supply_def `{!lcGS hlc Σ} (n : nat) : iProp Σ :=
  if hlc is HasLc then own lcGS_name (● n) else ⌜ n = 0 ⌝.
Local Definition lc_supply_aux : seal (@lc_supply_def). Proof. by eexists. Qed.
Local Definition lc_supply := lc_supply_aux.(unseal).
Local Definition lc_supply_unseal :
  @lc_supply = @lc_supply_def := lc_supply_aux.(seal_eq).
Global Arguments lc_supply {hlc Σ _} n.

Local Lemma lc_no_lc `{!lcGS HasNoLc Σ} n : £ n ⊣⊢ True.
Proof. by rewrite lc_unseal. Qed.
Local Lemma lc_supply_no_lc `{!lcGS HasNoLc Σ} n : lc_supply n ⊣⊢ ⌜ n = 0 ⌝.
Proof. by rewrite lc_supply_unseal. Qed.

(** The splitting rules for [£] hold regardless of whether later credits are
enabled. If later credits are disabled ([hlc = HasNoLc], these rules are not
useful on their own, but they can be used to write adequacy/soundness proof that
are generic in the choice of [hlc]. *)
Section lc_rules.
  Context `{!lcGS hlc Σ}.

  Lemma lc_split n m : £ (n + m) ⊣⊢ £ n ∗ £ m.
  Proof.
    rewrite lc_unseal /lc_def. destruct hlc; [|by iSplit; auto].
    rewrite -own_op auth_frag_op //=.
  Qed.

  Lemma lc_zero : ⊢ |==> £ 0.
  Proof.
    rewrite lc_unseal /lc_def. destruct hlc; [|by auto]. iApply own_unit.
  Qed.

  Lemma lc_succ n : £ (S n) ⊣⊢ £ 1 ∗ £ n.
  Proof. rewrite -lc_split //=. Qed.

  Lemma lc_weaken {n} m : m ≤ n → £ n -∗ £ m.
  Proof. intros [k ->]%Nat.le_sum. rewrite lc_split. iIntros "[$ _]". Qed.

  Global Instance lc_timeless n : Timeless (£ n).
  Proof. rewrite lc_unseal /lc_def. apply _. Qed.

  Global Instance lc_0_persistent : Persistent (£ 0).
  Proof. rewrite lc_unseal /lc_def. apply _. Qed.

  (** Make sure that the rule for [+] is used before [S], otherwise Rocq's
  unification applies the [S] hint too eagerly. See Iris issue #470. *)
  Global Instance from_sep_lc_add n m : FromSep (£ (n + m)) (£ n) (£ m) | 0.
  Proof. by rewrite /FromSep lc_split. Qed.
  Global Instance from_sep_lc_S n : FromSep (£ (S n)) (£ 1) (£ n) | 1.
  Proof. by rewrite /FromSep (lc_succ n). Qed.

  (** When combining later credits with [iCombine], the priorities are
  reversed when compared to [FromSep] and [IntoSep]. This causes
  [£ n] and [£ 1] to be combined as [£ (S n)], not as [£ (n + 1)]. *)
  Global Instance combine_sep_lc_add n m :
    CombineSepAs (£ n) (£ m) (£ (n + m)) | 1.
  Proof. by rewrite /CombineSepAs lc_split. Qed.
  Global Instance combine_sep_lc_S_l n :
    CombineSepAs (£ n) (£ 1) (£ (S n)) | 0.
  Proof. by rewrite /CombineSepAs comm (lc_succ n). Qed.

  Global Instance into_sep_lc_add n m : IntoSep (£ (n + m)) (£ n) (£ m) | 0.
  Proof. by rewrite /IntoSep lc_split. Qed.
  Global Instance into_sep_lc_S n : IntoSep (£ (S n)) (£ 1) (£ n) | 1.
  Proof. by rewrite /IntoSep (lc_succ n). Qed.
End lc_rules.

(** The (internal) [lc_supply] rules are only vald if later credits are enabled. *)
Section lc_supply_rules.
  Context `{!lcGS HasLc Σ}.

  Local Lemma lc_supply_bound n m : lc_supply m -∗ £ n -∗ ⌜n ≤ m⌝.
  Proof.
    rewrite lc_unseal /lc_def lc_supply_unseal /lc_supply_def.
    iIntros "H1 H2". iCombine "H1 H2" gives %Hop.
    iPureIntro. eapply auth_both_valid_discrete in Hop as [Hlt _].
    by eapply nat_included.
  Qed.

  Local Lemma lc_decrease_supply n m :
    lc_supply (n + m) -∗ £ n ==∗ lc_supply m.
  Proof.
    rewrite lc_unseal /lc_def lc_supply_unseal /lc_supply_def.
    iIntros "H1 H2". iMod (own_update_2 with "H1 H2") as "Hown".
    { eapply auth_update. eapply (nat_local_update _ _ m 0). lia. }
    by iDestruct "Hown" as "[Hm _]".
  Qed.

 Local Lemma lc_increase_supply n m :
    lc_supply m ==∗ lc_supply (n + m) ∗ £ n.
  Proof.
    rewrite lc_unseal /lc_def lc_supply_unseal /lc_supply_def.
    iIntros "H"; iMod (own_update with "H") as "Hown".
    { eapply auth_update_alloc. eapply (nat_local_update m 0 (n + m) n). lia. }
    iDestruct "Hown" as "[Hm ?]"; by iFrame.
  Qed.
End lc_supply_rules.

(** The later-elimination update *)
(** Let users import the above without also getting the below laws.
This should only be imported by the internal development of fancy updates. *)
Module le_upd.
  Definition le_upd_pre `{!lcGS hlc Σ} (P le_upd : iProp Σ) : iProp Σ :=
    ∀ n, lc_supply n ==∗
      (** Case 1: Generalization of except-0 [◇], needed for proving the rule
      [le_upd_keep]. There we obtain [▷^n ◇ P] for a timeless [P], and need to
      eliminate [n] laters and one except-0, which can be done by having a
      disjunct [▷^(S n) False] in the goal. *)
      ▷^(S n) False ∨
      (** Case 2: No credits are spent. *)
      (lc_supply n ∗ P) ∨
      (** Case 3: Eliminate a later by decreasing the credit supply (which
      means at least one credit needs to be spent). This case is impossible if
      later credits are disabled ([HasNoLc]), because [m < 0] is false. *)
      (∃ m, ⌜m < n⌝ ∗ lc_supply m ∗ ▷ le_upd).

  Local Instance le_upd_pre_contractive `{!lcGS hlc Σ} P : Contractive (le_upd_pre P).
  Proof. solve_contractive. Qed.
  Local Definition le_upd_def `{!lcGS hlc Σ} (P : iProp Σ) : iProp Σ :=
    fixpoint (le_upd_pre P).
  Local Definition le_upd_aux : seal (@le_upd_def). Proof. by eexists. Qed.
  Definition le_upd := le_upd_aux.(unseal).
  Local Definition le_upd_unseal : @le_upd = @le_upd_def := le_upd_aux.(seal_eq).
  Global Arguments le_upd {_ _ _} _.
  Notation "'|==£>' P" := (le_upd P)
    (at level 20, P at level 200, format "|==£>  P") : bi_scope.

  Local Lemma le_upd_unfold `{!lcGS hlc Σ} P :
    (|==£> P) ⊣⊢
    ∀ n, lc_supply n ==∗
         ▷^(S n) False ∨ (lc_supply n ∗ P) ∨ (∃ m, ⌜m < n⌝ ∗ lc_supply m ∗ ▷ |==£> P).
  Proof.
    by rewrite le_upd_unseal
      /le_upd_def {1}(fixpoint_unfold (le_upd_pre P)) {1}/le_upd_pre.
  Qed.

  (** If later credits are disabled, this lemma shows that [le_upd] is just the
  basic update + except-0 modality, i.e., fancy updates are like Iris 3.0. *)
  Local Lemma le_upd_unfold_no_le `{!lcGS HasNoLc Σ} P : (|==£> P) ⊣⊢ |==> ◇ P.
  Proof.
    rewrite le_upd_unfold. setoid_rewrite lc_supply_no_lc. iSplit.
    - iIntros "H".
      iMod ("H" $! 0 with "[//]") as "[>[]|[[_ ?]|(%m&%Hm&_)]]"; auto with lia.
    - iIntros "H %n ->". rewrite /bi_except_0. iMod "H" as "[?|?]"; auto.
  Qed.

  Section le_upd.
    Context `{!lcGS hlc Σ}.
    Implicit Types (P Q : iProp Σ).

    (** Rules for the later elimination update *)
    Global Instance le_upd_ne : NonExpansive le_upd.
    Proof.
      intros n; induction (lt_wf n) as [n _ IH].
      intros P1 P2 HP. rewrite (le_upd_unfold P1) (le_upd_unfold P2).
      do 10 (done || f_equiv). f_contractive. by eapply IH, dist_lt.
    Qed.

    Lemma bupd_le_upd P : (|==> P) ⊢ |==£> P.
    Proof.
      rewrite le_upd_unfold; iIntros "HP" (n) "Hpr".
      iMod "HP" as "HP". auto with iFrame.
    Qed.

    Lemma except_0_le_upd P : ◇ (|==£> P) ⊢ |==£> P.
    Proof.
      rewrite /bi_except_0. iIntros "[HFalse|$]".
      iApply le_upd_unfold; iIntros (n) "_ !>". iLeft. by iNext.
    Qed.

    Lemma le_upd_bind P Q : (P -∗ |==£> Q) -∗ (|==£> P) -∗ |==£> Q.
    Proof.
      iLöb as "IH". iIntros "HPQ".
      iEval (rewrite (le_upd_unfold P) (le_upd_unfold Q)).
      iIntros "HP" (n) "Hpr".
      iMod ("HP" with "Hpr") as "[?|[[Hpr HP]|HP]]"; first by auto.
      - iEval (rewrite le_upd_unfold) in "HPQ". by iApply ("HPQ" with "HP").
      - iModIntro. do 2 iRight. iDestruct "HP" as (n') "($ & $ & HP)".
        iNext. by iApply ("IH" with "HPQ HP").
    Qed.

    (** Derived lemmas *)
    Lemma le_upd_intro P : P ⊢ |==£> P.
    Proof. iIntros "H". by iApply bupd_le_upd. Qed.

    Lemma le_upd_mono P Q : (P ⊢ Q) → (|==£> P) ⊢ |==£> Q.
    Proof.
      intros Hent. iApply le_upd_bind.
      iIntros "P"; iApply le_upd_intro; by iApply Hent.
    Qed.

    Global Instance le_upd_mono' : Proper ((⊢) ==> (⊢)) le_upd.
    Proof. intros P Q PQ; by apply le_upd_mono. Qed.
    Global Instance le_upd_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) le_upd.
    Proof. intros P Q PQ; by apply le_upd_mono. Qed.
    Global Instance le_upd_equiv_proper : Proper ((≡) ==> (≡)) le_upd.
    Proof. apply ne_proper. apply _. Qed.

    Lemma le_upd_trans P : (|==£> |==£> P) ⊢ |==£> P.
    Proof.
      iIntros "HP". iApply le_upd_bind; eauto.
    Qed.
    Lemma le_upd_frame_r P R : (|==£> P) ∗ R ⊢ |==£> P ∗ R.
    Proof.
      iIntros "[Hupd R]". iApply (le_upd_bind with "[R]"); last done.
      iIntros "P". iApply le_upd_intro. by iFrame.
    Qed.
    Lemma le_upd_frame_l P R : R ∗ (|==£> P) ⊢ |==£> R ∗ P.
    Proof. rewrite comm le_upd_frame_r comm //. Qed.

    (** A safety check that later-elimination updates can replace basic updates *)
    (** We do not use this to build an instance, because it would conflict
       with the basic updates. *)
    Local Lemma bi_bupd_mixin_le_upd : BiBUpdMixin (iPropI Σ) le_upd.
    Proof.
      split; rewrite /bupd.
      - apply _.
      - apply le_upd_intro.
      - apply le_upd_mono.
      - apply le_upd_trans.
      - apply le_upd_frame_r.
    Qed.

    (** Proof mode class instances internally needed for people defining their
    [fupd] with [le_upd]. *)
    Global Instance elim_bupd_le_upd p P Q :
      ElimModal True p false (|==> P) P (|==£> Q) (|==£> Q).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim //=.
      rewrite bupd_le_upd. iIntros "_ [HP HPQ]".
      iApply (le_upd_bind with "HPQ HP").
    Qed.

    Global Instance from_assumption_le_upd p P Q :
      FromAssumption p P Q → KnownRFromAssumption p P (|==£> Q).
    Proof.
      rewrite /KnownRFromAssumption /FromAssumption=>->. apply le_upd_intro.
    Qed.

    Global Instance from_pure_le_upd a P φ :
      FromPure a P φ → FromPure a (|==£> P) φ.
    Proof. rewrite /FromPure=> <-. apply le_upd_intro. Qed.

    Global Instance is_except_0_le_upd P : IsExcept0 (le_upd P).
    Proof. apply except_0_le_upd. Qed.

    Global Instance from_modal_le_upd P :
      FromModal True modality_id (|==£> P) (|==£> P) P.
    Proof. by rewrite /FromModal /= -le_upd_intro. Qed.

    Global Instance elim_modal_le_upd p P Q :
      ElimModal True p false (|==£> P) P (|==£> Q) (|==£> Q).
    Proof.
      by rewrite /ElimModal
        intuitionistically_if_elim le_upd_frame_r wand_elim_r le_upd_trans.
    Qed.

    Global Instance frame_le_upd p R P Q :
      Frame p R P Q → Frame p R (|==£> P) (|==£> Q).
    Proof. rewrite /Frame=><-. by rewrite le_upd_frame_l. Qed.
  End le_upd.

  Lemma lc_le_upd_elim_later `{!lcGS HasLc Σ} P : £ 1 -∗ (▷ P) -∗ |==£> P.
  Proof.
    iIntros "Hc Hl". iApply le_upd_unfold. iIntros (n) "Hs". do 2 iRight.
    iDestruct (lc_supply_bound with "Hs Hc") as "%".
    replace n with (1 + (n - 1)) by lia.
    iMod (lc_decrease_supply with "Hs Hc") as "$"; iModIntro.
    iSplit; [by eauto with lia|]. iNext. by iApply bupd_le_upd.
  Qed.

  Lemma lc_le_upd_add_later `{!lcGS HasLc Σ} P : £ 1 -∗ ▷ (|==£> P) -∗ |==£> P.
  Proof.
    iIntros "H£ H". iApply le_upd_trans.
    by iApply (lc_le_upd_elim_later with "H£").
  Qed.

  (** You probably do NOT want to use these lemmas; use [lc_soundness] if you
  want to actually use [le_upd]! *)
  Local Lemma lc_alloc `{!lcGpreS Σ} n :
    ⊢ |==> ∃ _ : lcGS HasLc Σ, lc_supply n ∗ £ n.
  Proof.
    rewrite lc_unseal /lc_def lc_supply_unseal /lc_supply_def.
    iMod (own_alloc (● n ⋅ ◯ n)) as (γLC) "[H● H◯]";
      first (apply auth_both_valid; split; done).
    iModIntro. iExists (LcGS HasLc _ _ γLC). iFrame.
  Qed.
  Local Lemma lc_alloc_no_lc `{!lcGpreS Σ} n :
    ⊢ ∃ _ : lcGS HasNoLc Σ, lc_supply 0 ∗ £ n.
  Proof.
    rewrite lc_unseal /lc_def lc_supply_unseal /lc_supply_def.
    (* Use [fresh] to pick *any* ghost name (it is unused anyway). *)
    by iExists (LcGS HasNoLc _ _ (fresh (∅ : gset gname))).
  Qed.

  (** Flexible soundness theorem through "finally" modality. *)
  (** The later-elimination finally modality [le_upd_finally] is used internally
  in the finally modality for fancy updates ([fupd_finally]). It should not be
  used directly by end-users. See the file [fancy_updates] for documentation how
  to prove soundness/adequacy results using the user-facing finally modality.

  Compared to the later-elimination modality [le_upd] itself, this modality
  only consumes the supply [lc_supply], but does not give it back. This change
  allows us to prove the rules [le_upd_finally_later], [le_upd_finally_keep],
  and [le_upd_finally_forall], which cannot be proven for [le_upd]. For instance,
  to prove [le_upd_finally_forall] the goal is [▷^m ◇ ■ ∀ x, Φ x] where we can
  just commute out the [∀]. Such a proof does not work for a corresponding lemma
  for [le_upd] because we cannot commute out the [∀].

  Due to the plain modality [■], we can perform basic updates around
  [le_upd_finally] (we have [(|==> ■ P) ⊣⊢ ■ P]). This fact is exposed by the
  rule [le_upd_le_upd_finally] combined with the rule [bupd_le_upd]. *)
  Definition le_upd_finally_def `{!lcGS hlc Σ} (P : iProp Σ) : iProp Σ :=
    ∀ m, lc_supply m -∗ ▷^m ◇ ■ P.
  Local Definition le_upd_finally_aux : seal (@le_upd_finally_def).
  Proof. by eexists. Qed.
  Local Definition le_upd_finally := le_upd_finally_aux.(unseal).
  Local Definition le_upd_finally_unseal :
    @le_upd_finally = @le_upd_finally_def := le_upd_finally_aux.(seal_eq).
  Global Arguments le_upd_finally {hlc Σ _}.

  Notation "|==£|■> Q" := (le_upd_finally Q) (at level 20, Q at level 200,
     format "'[  ' |==£|■>  '/' Q ']'") : bi_scope.

  Section le_upd_finally.
    Context `{!lcGS hlc Σ}.

    Global Instance le_upd_finally_ne : NonExpansive le_upd_finally.
    Proof. rewrite le_upd_finally_unseal. solve_proper. Qed.

    Lemma le_upd_finally_mono P Q : (P ⊢ Q) → (|==£|■> P) ⊢ (|==£|■> Q).
    Proof. rewrite le_upd_finally_unseal. solve_proper. Qed.

    Lemma le_upd_finally_intro P : ■ P ⊢ |==£|■> P.
    Proof. rewrite le_upd_finally_unseal. iIntros "#HP %m _ !> !>". done. Qed.

    Lemma le_upd_le_upd_finally P : (|==£> |==£|■> P) ⊢ |==£|■> P.
    Proof.
      rewrite le_upd_finally_unseal /le_upd_finally_def. iIntros "HP %m Hlc".
      iLöb as "IH" forall (m).
      iEval (rewrite le_upd_unfold) in "HP".
      iMod ("HP" with "Hlc") as "[HFalse|[[Hlc H]|(%m' & %Hm & Hlc & H)]]".
      { iNext. by iMod "HFalse". }
      { by iApply "H". }
      replace m with (S ((m - m' - 1) + m')) by lia. rewrite /= laterN_add.
      do 2 iNext. iApply ("IH" with "H Hlc").
    Qed.

    Lemma le_upd_finally_except_0 P : (|==£|■> ◇ P) ⊢ |==£|■> P.
    Proof.
      rewrite le_upd_finally_unseal /le_upd_finally_def. iIntros "HP %m Hlc".
      iEval (rewrite -except_0_idemp except_0_plainly). by iApply "HP".
    Qed.

    (** Commute a later out of the modality. This only works if the proposition
    below the later can be turned into an except-0 [◇]. *)
    Lemma le_upd_finally_later P : ▷ (|==£|■> P) ⊢ |==£|■> ▷ ◇ P.
    Proof.
      rewrite le_upd_finally_unseal /le_upd_finally_def. iIntros "H %m Hlc".
      iEval (rewrite -later_plainly -except_0_plainly
        -except_0_intro -laterN_later /=).
      iNext. by iApply "H".
    Qed.

    (** Add a later credit by removing a later below the modality. This
    only works if the proposition below the later can be turned into an
    except-0 [◇]. *)
    Lemma le_upd_finally_add_lc P : (£ 1 -∗ |==£|■> P) ⊢ |==£|■> ▷ ◇ P.
    Proof.
      rewrite le_upd_finally_unseal. iIntros "H %m Hlc".
      rewrite -except_0_intro -later_plainly -except_0_plainly -laterN_later.
      destruct hlc.
      - iMod (later_credits.lc_increase_supply 1 with "Hlc") as "[Hlc H£]".
        iApply ("H" with "H£ Hlc").
      - iIntros "/= !>". iApply ("H" with "[] Hlc"). by iApply lc_no_lc.
    Qed.

    Lemma le_upd_finally_forall {A} (Φ : A → iProp Σ) :
      (∀ x, |==£|■> Φ x) ⊢ |==£|■> ∀ x, Φ x.
    Proof.
      rewrite le_upd_finally_unseal.
      iIntros "H %m Hlc %x". iApply ("H" with "Hlc").
    Qed.

    (* [iApply] this lemma to use your current context for proving a (timeless)
    assertion [P] *without* actually using up the context. You can then continue
    the proof in the second conjunct. *)
    Lemma le_upd_keep P `{!TCOr (TCEq hlc HasNoLc) (Timeless P)} Q :
      (|==£|■> P) ∧ (P -∗ |==£> Q) ⊢ |==£> Q.
    Proof.
      iIntros "H". iApply le_upd_unfold; iIntros (n) "Hc".
      iAssert (▷^(S n) False ∨ ■ P)%I as "#[Hfalse|HP]"; [|by auto|].
      { iDestruct "H" as "[H _]". rewrite le_upd_finally_unseal.
        destruct select (TCOr _ _) as [->%TCEq_eq|?].
        - iDestruct (lc_supply_no_lc with "Hc") as %->; simpl.
          iApply ("H" with "Hc").
        - iApply (timeless_laterN _ (S n)). iSpecialize ("H" with "Hc").
          by iEval (rewrite except_0_into_later -laterN_later) in "H". }
      iDestruct "H" as "[_ H]". by iApply (le_upd_unfold with "(H [//])").
    Qed.

    (** Derived rules *)
    (** Since the modality is used only internally in the version for fancy
    updates, we do not provide instances of the proof mode classes. *)
    Global Instance le_upd_finally_proper : Proper ((⊣⊢) ==> (⊣⊢)) le_upd_finally.
    Proof. apply: ne_proper. Qed.
    Global Instance le_upd_finally_mono' : Proper ((⊢) ==> (⊢)) le_upd_finally.
    Proof. intros P Q. apply le_upd_finally_mono. Qed.
    Global Instance le_upd_finally_flip_mono' :
      Proper (flip (⊢) ==> flip (⊢)) le_upd_finally.
    Proof. intros P Q. apply le_upd_finally_mono. Qed.
  End le_upd_finally.

  Lemma le_upd_finally_soundness hlc `{!lcGpreS Σ} n P :
    (∀ `{!lcGS hlc Σ}, £ n ⊢ |==£|■> P) → ⊢ P.
  Proof.
    rewrite le_upd_finally_unseal. intros HP. destruct hlc.
    - apply (laterN_soundness _ (S n)).
      rewrite laterN_later -except_0_into_later -(plainly_elim P).
      iMod (lc_alloc n) as (Hc) "[Hlc H£]". iApply (HP with "H£ Hlc").
    - apply (laterN_soundness _ 1).
      iDestruct (lc_alloc_no_lc n) as (Hc) "[Hlc H£]".
      by iMod (HP with "H£ Hlc") as "H".
  Qed.

  #[deprecated(note="Internal result, will be removed in the future. Use
  `le_upd_finally_soundness` if you build a custom update modality.")]
  Lemma lc_soundness hlc `{!lcGpreS Σ} m (P : iProp Σ) `{!Plain P} :
    (∀ `{!lcGS hlc Σ}, £ m -∗ |==£> P) → ⊢ P.
  Proof.
    intros H. apply (le_upd_finally_soundness hlc m); iIntros (?) "H£".
    iApply le_upd_le_upd_finally. iMod (H with "H£") as "HP"; iModIntro.
    iApply le_upd_finally_intro. by iApply plain_plainly.
  Qed.
End le_upd.
