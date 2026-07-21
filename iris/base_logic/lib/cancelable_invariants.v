From iris.algebra Require Export frac excl.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export invariants.

(* This is using a pair of options to represent two pieces of ghost state (the
 * fractional invariant token and an internal exclusive token) using one ghost
 * name. The exclusive token is used to prove `cinv_acc_1`. *)
Class cinvG Σ := { 
  #[local] cinv_inG :: inG Σ (prodR (optionR (exclR unitO)) (optionR dfracR)) ;
}.

Definition cinvΣ : gFunctors :=
  #[GFunctor (prodR (optionR (exclR unitO)) (optionR dfracR))].

Global Instance subG_cinvΣ {Σ} : subG cinvΣ Σ → cinvG Σ.
Proof. solve_inG. Qed.

Section defs.
  Context `{!invGS_gen hlc Σ, !cinvG Σ}.

  Definition cinv_own (γ : gname) (p : frac) : iProp Σ :=
    own γ (None, Some (DfracOwn p)).
  Definition cinv_excl γ : iProp Σ := own γ (Some (Excl ()), None).

  Definition cinv (N : namespace) (γ : gname) (P : iProp Σ) : iProp Σ :=
    inv N (cinv_own γ 1 ∨ P ∗ cinv_excl γ).
End defs.

Global Instance: Params (@cinv) 5 := {}.

Section proofs.
  Context `{!invGS_gen hlc Σ, !cinvG Σ}.

  Global Instance cinv_own_timeless γ p : Timeless (cinv_own γ p).
  Proof. rewrite /cinv_own; apply _. Qed.

  Global Instance cinv_contractive N γ : Contractive (cinv N γ).
  Proof. solve_contractive. Qed.
  Global Instance cinv_ne N γ : NonExpansive (cinv N γ).
  Proof. exact: contractive_ne. Qed.
  Global Instance cinv_proper N γ : Proper ((≡) ==> (≡)) (cinv N γ).
  Proof. exact: ne_proper. Qed.

  Global Instance cinv_persistent N γ P : Persistent (cinv N γ P).
  Proof. rewrite /cinv; apply _. Qed.

  Global Instance cinv_own_fractional γ : Fractional (cinv_own γ).
  Proof. intros ??. by rewrite /cinv_own -own_op. Qed.
  Global Instance cinv_own_as_fractional γ q :
    AsFractional (cinv_own γ q) (cinv_own γ) q.
  Proof. split; [done|]. apply _. Qed.

  Lemma cinv_own_valid γ q1 q2 : cinv_own γ q1 -∗ cinv_own γ q2 -∗ ⌜q1 + q2 ≤ 1⌝%Qp.
  Proof.
    rewrite bi.wand_curry -own_op own_valid.
    iIntros "%H !%". apply H.
  Qed.

  Lemma cinv_own_excl_alloc P :
    pred_infinite P → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ cinv_excl γ ∗ cinv_own γ 1.
  Proof.
    intros HP. setoid_rewrite <-own_op. apply own_alloc_strong; done.
  Qed.

  Lemma cinv_own_1_l γ q : cinv_own γ 1 -∗ cinv_own γ q -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (cinv_own_valid with "H1 H2") as %[]%(exclusive_l 1%Qp).
  Qed.

  Lemma cinv_excl_excl γ : cinv_excl γ -∗ cinv_excl γ -∗ False.
  Proof.
    rewrite bi.wand_curry -own_op own_valid -pair_op.
    iIntros "%H !%". apply H.
  Qed.

  Lemma cinv_iff N γ P Q : cinv N γ P -∗ ▷ □ (P ↔ Q) -∗ cinv N γ Q.
  Proof.
    iIntros "HI #HPQ". iApply (inv_iff with "HI"). iIntros "!> !>".
    iSplit; iIntros "[$|[? ?]]"; iRight; iFrame; by iApply "HPQ".
  Qed.

  (*** Allocation rules. *)
  (** The "strong" variants permit any infinite [I], and choosing [P] is delayed
  until after [γ] was chosen.*)
  Lemma cinv_alloc_strong (I : gname → Prop) E N :
    pred_infinite I →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗ ∀ P, ▷ P ={E}=∗ cinv N γ P.
  Proof.
    iIntros (?). iMod cinv_own_excl_alloc as (γ) "[$ [Hexcl $]]"; first done.
    iIntros "!>" (P) "P". iApply inv_alloc. iRight. iFrame.
  Qed.

  (** The "open" variants create the invariant in the open state, and delay
  having to prove [P].
  These do not imply the other variants because of the extra assumption [↑N ⊆ E]. *)
  Lemma cinv_alloc_strong_open (I : gname → Prop) E N :
    pred_infinite I →
    ↑N ⊆ E →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗ ∀ P,
      |={E,E∖↑N}=> cinv N γ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (??). iMod (cinv_own_excl_alloc I) as (γ) "[$ [Hexcl $]]"; first done.
    iIntros "!>" (P). iMod inv_alloc_open as "[$ Hclose]"; first done.
    iIntros "!> P". iApply "Hclose". iRight. iFrame.
  Qed.

  Lemma cinv_alloc_cofinite (G : gset gname) E N :
    ⊢ |={E}=> ∃ γ, ⌜ γ ∉ G ⌝ ∗ cinv_own γ 1 ∗ ∀ P, ▷ P ={E}=∗ cinv N γ P.
  Proof.
    apply cinv_alloc_strong. apply (pred_infinite_set (C:=gset gname))=> E'.
    exists (fresh (G ∪ E')). apply not_elem_of_union, is_fresh.
  Qed.

  Lemma cinv_alloc E N P : ▷ P ={E}=∗ ∃ γ, cinv N γ P ∗ cinv_own γ 1.
  Proof.
    iIntros "HP". iMod (cinv_alloc_cofinite ∅ E N) as (γ _) "[Hγ Halloc]".
    iExists γ. iFrame "Hγ". by iApply "Halloc".
  Qed.

  Lemma cinv_alloc_open E N P :
    ↑N ⊆ E → ⊢ |={E,E∖↑N}=> ∃ γ, cinv N γ P ∗ cinv_own γ 1 ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?). iMod (cinv_alloc_strong_open (λ _, True)) as (γ) "(_ & Htok & Hmake)"; [|done|].
    { apply pred_infinite_True. }
    iMod ("Hmake" $! P) as "[Hinv Hclose]". iIntros "!>". iExists γ. iFrame.
  Qed.

  (*** Accessors *)

  (* If we any fraction of the invariant token, then we can open the invariant
  * atomically. *)
  Lemma cinv_acc_strong E N γ p P :
    ↑N ⊆ E →
    cinv N γ P -∗ (cinv_own γ p ={E,E∖↑N}=∗
    ▷ P ∗ cinv_own γ p ∗ (∀ E' : coPset, ▷ P ∨ cinv_own γ 1 ={E',↑N ∪ E'}=∗ True)).
  Proof.
    iIntros (?) "Hinv Hown".
    iMod (inv_acc_strong with "Hinv") as "[[>Hown'|[$ >Hexcl]] H]"; first done.
    { iDestruct (cinv_own_1_l with "Hown' Hown") as %[]. }
    iIntros "{$Hown} !>" (E') "[P|Hown]"; iApply "H"; eauto with iFrame.
  Qed.

  Lemma cinv_acc E N γ p P :
    ↑N ⊆ E →
    cinv N γ P -∗ cinv_own γ p ={E,E∖↑N}=∗ ▷ P ∗ cinv_own γ p ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "#Hinv Hγ".
    iMod (cinv_acc_strong with "Hinv Hγ") as "($ & $ & H)"; first done.
    iIntros "!> HP".
    iMod ("H" with "[$HP]") as "_".
    rewrite -union_difference_L //.
  Qed.

  (* If we temporarily give up the invariant token at fraction 1, then we can
   * open the invariant non-atomically. *)
  Lemma cinv_acc_1 E N γ P :
    ↑N ⊆ E →
    cinv N γ P -∗ 
    cinv_own γ 1 ={E}=∗ 
    ▷ P ∗ (∀ E', ⌜↑N ⊆ E'⌝ -∗ ▷P ={E'}=∗ cinv_own γ 1).
  Proof.
    iIntros (?) "#Hinv Hγ".
    iInv "Hinv" as "[>Hγ'|[$ >Hexcl]]" "Hclose".
    { iDestruct (cinv_own_1_l with "Hγ Hγ'") as %[]. }
    iMod ("Hclose" with "[$Hγ]") as "_". iIntros "!>" (E' HE') "HP".
    iInv "Hinv" as "[>$|[_ >Hexcl']]" "Hclose".
    - iApply "Hclose". eauto with iFrame.
    - iDestruct (cinv_excl_excl with "Hexcl Hexcl'") as %[].
  Qed.

  (*** Other *)
  Lemma cinv_cancel E N γ P :
    ↑N ⊆ E → cinv N γ P -∗ cinv_own γ 1 ={E}=∗ ▷ P.
  Proof.
    iIntros (?) "#Hinv Hγ".
    by iDestruct (cinv_acc_1 with "[$] [$]") as "[$ _]".
  Qed.

  Lemma cinv_inv N γ q P :
    cinv N γ P -∗ cinv_own γ q ==∗ inv N P.
  Proof.
    iIntros "#Hinv Htok".
    iAssert (own γ (None, Some DfracDiscarded)) with "[> Htok]" as "#Htok".
    { iApply (own_update with "Htok").
      apply prod_update; simpl; first done.
      apply option_update.
      apply dfrac_discard_update. }
    iModIntro. iApply (inv_alter with "Hinv").
    iIntros "!> !> [Htok2|[$ Hexcl]]".
    { iExFalso. iCombine "Htok Htok2" gives %[_ ?]. done. }
    iIntros "HP". iRight. by iFrame.
  Qed.

  Global Instance into_inv_cinv N γ P : IntoInv (cinv N γ P) N := {}.

  Global Instance into_acc_cinv E N γ P p :
    IntoAcc (X:=unit) (cinv N γ P)
            (↑N ⊆ E) (cinv_own γ p) (fupd E (E∖↑N)) (fupd (E∖↑N) E)
            (λ _, ▷ P ∗ cinv_own γ p)%I (λ _, ▷ P)%I (λ _, None)%I.
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit -assoc.
    iIntros (?) "#Hinv Hown". by iApply cinv_acc.
  Qed.
End proofs.

Global Typeclasses Opaque cinv_own cinv.
