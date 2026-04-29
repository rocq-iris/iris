From stdpp Require Export coPset nat_cancel.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import coq_tactics proofmode reduction.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import wsat.
From iris.base_logic Require Export later_credits.
From iris.prelude Require Import options.
Export wsatGS.
Import uPred.
Import le_upd_if.

(** The definition of fancy updates (and in turn the logic built on top of it) is parameterized
    by whether it supports elimination of laters via later credits or not.
    This choice is necessary as the fancy update *with* later credits does *not* support
    the interaction laws with the plainly modality in [BiFUpdPlainly]. While these laws are
    seldomly used, support for them is required for backwards compatibility.

    Thus, the [invGS_gen] typeclass ("gen" for "generalized") is parameterized by
    a parameter of type [has_lc] that determines whether later credits are
    available or not. [invGS] is provided as a convenient notation for the default [HasLc].
    We don't use that notation in this file to avoid confusion.
 *)
Inductive has_lc := HasLc | HasNoLc.

Class invGpreS (Σ : gFunctors) : Set := InvGpreS {
  #[local] invGpreS_wsat :: wsatGpreS Σ;
  #[local] invGpreS_lc :: lcGpreS Σ;
}.

(* [invGS_lc] needs to be global in order to enable the use of lemmas like
[lc_split] that require [lcGS], and not [invGS]. [invGS_wsat] also needs to be
global as the lemmas in [invariants.v] require it. *)
Class invGS_gen (hlc : has_lc) (Σ : gFunctors) : Set := InvG {
  #[global] invGS_wsat :: wsatGS Σ;
  #[global] invGS_lc :: lcGS Σ;
}.
Global Hint Mode invGS_gen - - : typeclass_instances.
Global Hint Mode invGpreS - : typeclass_instances.

Notation invGS := (invGS_gen HasLc).

Definition invΣ : gFunctors :=
  #[wsatΣ; lcΣ].
Global Instance subG_invΣ {Σ} : subG invΣ Σ → invGpreS Σ.
Proof. solve_inG. Qed.

Local Definition uPred_fupd_def `{!invGS_gen hlc Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  wsat ∗ ownE E1 -∗ le_upd_if (if hlc is HasLc then true else false) (◇ (wsat ∗ ownE E2 ∗ P)).
Local Definition uPred_fupd_aux : seal (@uPred_fupd_def). Proof. by eexists. Qed.
Definition uPred_fupd := uPred_fupd_aux.(unseal).
Global Arguments uPred_fupd {hlc Σ _}.
Local Lemma uPred_fupd_unseal `{!invGS_gen hlc Σ} : @fupd _ uPred_fupd = uPred_fupd_def.
Proof. rewrite -uPred_fupd_aux.(seal_eq) //. Qed.

Lemma uPred_fupd_mixin `{!invGS_gen hlc Σ} : BiFUpdMixin (uPredI (iResUR Σ)) uPred_fupd.
Proof.
  split.
  - rewrite uPred_fupd_unseal. solve_proper.
  - intros E1 E2 (E1''&->&?)%subseteq_disjoint_union_L.
    rewrite uPred_fupd_unseal /uPred_fupd_def ownE_op //.
    by iIntros "($ & $ & HE) !> !> [$ $] !> !>".
  - rewrite uPred_fupd_unseal.
    iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
  - rewrite uPred_fupd_unseal.
    iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
  - rewrite uPred_fupd_unseal. iIntros (E1 E2 E3 P) "HP HwE".
    iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
  - intros E1 E2 Ef P HE1Ef. rewrite uPred_fupd_unseal /uPred_fupd_def ownE_op //.
    iIntros "Hvs (Hw & HE1 &HEf)".
    iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
    iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
    iIntros "!> !>". by iApply "HP".
  - rewrite uPred_fupd_unseal /uPred_fupd_def. by iIntros (????) "[HwP $]".
Qed.
Global Instance uPred_bi_fupd `{!invGS_gen hlc Σ} : BiFUpd (uPredI (iResUR Σ)) :=
  {| bi_fupd_mixin := uPred_fupd_mixin |}.

Global Instance uPred_bi_bupd_fupd `{!invGS_gen hlc Σ} : BiBUpdFUpd (uPredI (iResUR Σ)).
Proof. rewrite /BiBUpdFUpd uPred_fupd_unseal. by iIntros (E P) ">? [$ $] !> !>". Qed.

(** The interaction laws with the plainly modality are only supported when
  we opt out of the support for later credits. *)
Global Instance uPred_bi_fupd_sbi_no_lc `{!invGS_gen HasNoLc Σ} :
  BiFUpdSbi (uPredI (iResUR Σ)).
Proof.
  split; rewrite uPred_fupd_unseal /uPred_fupd_def.
  - iIntros (E E' Pi Q) "[H HQ] [Hw HE]".
    iAssert (◇ <si_pure> Pi)%I as "#>HP".
    { by iMod ("H" with "HQ [$]") as "(_ & _ & HP)". }
    by iFrame.
  - iIntros (E Pi) "H [Hw HE]".
    iAssert (▷ ◇ <si_pure> Pi)%I as "#HP".
    { iNext. by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    iFrame. iIntros "!> !> !>". by iMod "HP".
  - iIntros (E A Φi) "HΦ [Hw HE]".
    iAssert (◇ ∀ x : A, <si_pure> Φi x)%I as "#>HP".
    { iIntros (x). by iMod ("HΦ" with "[$Hw $HE]") as "(_&_&?)". }
    by iFrame.
Qed.

(** Later credits: the laws are only available when we opt into later credit support.*)

(** [lc_fupd_elim_later] allows to eliminate a later from a hypothesis at an update.
  This is typically used as [iMod (lc_fupd_elim_later with "Hcredit HP") as "HP".],
  where ["Hcredit"] is a credit available in the context and ["HP"] is the
  assumption from which a later should be stripped. *)
Lemma lc_fupd_elim_later `{!invGS_gen HasLc Σ} E P :
   £ 1 -∗ (▷ P) -∗ |={E}=> P.
Proof.
  iIntros "Hf Hupd".
  rewrite uPred_fupd_unseal /uPred_fupd_def.
  iIntros "[$ $]". iApply (le_upd_later with "Hf").
  iNext. by iModIntro.
Qed.

(** If the goal is a fancy update, this lemma can be used to make a later appear
  in front of it in exchange for a later credit.
  This is typically used as [iApply (lc_fupd_add_later with "Hcredit")],
  where ["Hcredit"] is a credit available in the context. *)
Lemma lc_fupd_add_later `{!invGS_gen HasLc Σ} E1 E2 P :
  £ 1 -∗ (▷ |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Proof.
  iIntros "Hf Hupd". iApply (fupd_trans E1 E1).
  iApply (lc_fupd_elim_later with "Hf Hupd").
Qed.

(** Similar to above, but here we are adding [n] laters. *)
Lemma lc_fupd_add_laterN `{!invGS_gen HasLc Σ} E1 E2 P n :
  £ n -∗ (▷^n |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Proof.
  iIntros "Hf Hupd". iInduction n as [|n] "IH"; first done.
  iDestruct "Hf" as "[H1 Hf]".
  iApply (lc_fupd_add_later with "H1"); iNext.
  iApply ("IH" with "[$] [$]").
Qed.

Lemma lc_fupd_add_step_fupdN `{!invGS_gen HasLc Σ} E1 E2 E3 P n :
  £ n -∗ (|={E1}[E2]▷=>^n |={E1,E3}=> P) -∗ |={E1,E3}=> P.
Proof.
  iIntros "Hf Hupd". iInduction n as [|n] "IH"; simpl; first done.
  iMod "Hupd". iDestruct "Hf" as "[H1 Hf]".
  iApply (lc_fupd_add_later with "H1"); iNext.
  iMod "Hupd". iApply ("IH" with "[$] [$]").
Qed.

(** * [fupd] soundness lemmas *)

(** "Unfolding" soundness stamement for no-LC fupd:
This exposes that when initializing the [invGS_gen], we can provide
a general lemma that lets one unfold a [|={E1, E2}=> P] into a basic update
while also carrying around some frame [ω E] that tracks the current mask.
We also provide a bunch of later credits for consistency,
but there is no way to use them since this is a [HasNoLc] lemma. *)
Lemma fupd_soundness_no_lc_unfold `{!invGpreS Σ} m E :
  ⊢ |==> ∃ `(Hws: invGS_gen HasNoLc Σ) (ω : coPset → iProp Σ),
    £ m ∗ ω E ∗ □ (∀ E1 E2 P, (|={E1, E2}=> P) -∗ ω E1 ==∗ ◇ (ω E2 ∗ P)).
Proof.
  iMod wsat_alloc as (Hw) "[Hw HE]".
  (* We don't actually want any credits, but we need the [lcGS]. *)
  iMod (later_credits.le_upd.lc_alloc m) as (Hc) "[_ Hlc]".
  set (Hi := InvG HasNoLc _ Hw Hc).
  iExists Hi, (λ E, wsat ∗ ownE E)%I.
  rewrite (union_difference_L E ⊤); [|set_solver].
  rewrite ownE_op; [|set_solver].
  iDestruct "HE" as "[HE _]". iFrame.
  iIntros "!>!>" (E1 E2 P) "HP HwE".
  rewrite fancy_updates.uPred_fupd_unseal
          /fancy_updates.uPred_fupd_def -assoc /=.
  by iApply ("HP" with "HwE").
Qed.

(** Note: the [_no_lc] soundness lemmas also allow generating later credits, but
  these cannot be used for anything. They are merely provided to enable making
  the adequacy proof generic in whether later credits are used. *)
Lemma fupd_soundness_no_lc `{!invGpreS Σ} E1 E2 (P : iProp Σ) `{!Plain P} m :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ={E1,E2}=∗ P) → ⊢ P.
Proof.
  intros Hfupd. apply later_soundness, bupd_soundness; [by apply later_plain|].
  iMod fupd_soundness_no_lc_unfold as (hws ω) "(Hlc & Hω & #H)".
  iMod ("H" with "[Hlc] Hω") as "H'".
  { iMod (Hfupd with "Hlc") as "H'". iModIntro. iApply "H'". }
  iDestruct "H'" as "[>H1 >H2]". by iFrame.
Qed.

Lemma fupd_soundness_lc `{!invGpreS Σ} n E1 E2 (P : iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !invGS_gen HasLc Σ}, £ n ={E1,E2}=∗ P) → ⊢ P.
Proof.
  intros Hfupd. eapply (lc_soundness (S n)); first done.
  intros Hc. rewrite lc_succ.
  iIntros "[Hone Hn]". rewrite -le_upd_trans. iApply bupd_le_upd.
  iMod wsat_alloc as (Hw) "[Hw HE]".
  set (Hi := InvG HasLc _ Hw Hc).
  iAssert (|={⊤,E2}=> P)%I with "[Hn]" as "H".
  { iMod (fupd_mask_subseteq E1) as "_"; first done. by iApply (Hfupd Hi). }
  rewrite uPred_fupd_unseal /uPred_fupd_def.
  iModIntro. iMod ("H" with "[$Hw $HE]") as "H".
  iPoseProof (except_0_into_later with "H") as "H".
  iApply (le_upd_later with "Hone"). iNext.
  iDestruct "H" as "(_ & _ & $)".
Qed.

(** Generic soundness lemma for the fancy update, parameterized by [use_credits]
  on whether to use credits or not. *)
Lemma fupd_soundness_gen `{!invGpreS Σ} (P : iProp Σ) `{!Plain P}
  (hlc : has_lc) n E1 E2 :
  (∀ `{Hinv : invGS_gen hlc Σ},
    £ n ={E1,E2}=∗ P) →
  ⊢ P.
Proof.
  destruct hlc.
  - apply fupd_soundness_lc. done.
  - apply fupd_soundness_no_lc. done.
Qed.

(** [step_fupdN] soundness lemmas *)

Lemma step_fupdN_soundness_no_lc `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n m :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ={⊤,∅}=∗ |={∅}▷=>^n P) →
  ⊢ P.
Proof.
  intros Hiter.
  apply (laterN_soundness _  (S n)); simpl.
  apply (fupd_soundness_no_lc ⊤ ⊤ _ m)=> Hinv. iIntros "Hc".
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  iApply fupd_plainly_mask. iSpecialize ("H" with "Hc").
  iMod (step_fupdN_plain with "H") as "H". iMod "H". iModIntro.
  rewrite -later_plainly -laterN_plainly -later_laterN laterN_later.
  iNext. iMod "H" as "#H". auto.
Qed.

Lemma step_fupdN_soundness_no_lc' `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n m :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ={⊤}[∅]▷=∗^n P) →
  ⊢ P.
Proof.
  intros Hiter. eapply (step_fupdN_soundness_no_lc _ n m)=>Hinv.
  iIntros "Hcred". destruct n as [|n].
  { by iApply fupd_mask_intro_discard; [|iApply (Hiter Hinv)]. }
   simpl in Hiter |- *. iMod (Hiter with "Hcred") as "H". iIntros "!>!>!>".
  iMod "H". clear. iInduction n as [|n] "IH"; [by iApply fupd_mask_intro_discard|].
  simpl. iMod "H". iIntros "!>!>!>". iMod "H". by iApply "IH".
Qed.

Lemma step_fupdN_soundness_lc `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n m :
  (∀ `{Hinv: !invGS_gen HasLc Σ}, £ m ={⊤,∅}=∗ |={∅}▷=>^n P) →
  ⊢ P.
Proof.
  intros Hiter.
  eapply (fupd_soundness_lc (m + n)); [apply _..|].
  iIntros (Hinv) "Hlc". rewrite lc_split.
  iDestruct "Hlc" as "[Hm Hn]". iMod (Hiter with "Hm") as "Hupd".
  clear Hiter.
  iInduction n as [|n] "IH"; simpl.
  - by iModIntro.
  - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]".
    iMod "Hupd". iMod (lc_fupd_elim_later with "Hone Hupd") as "> Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.

Lemma step_fupdN_soundness_lc' `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n m :
  (∀ `{Hinv: !invGS_gen hlc Σ}, £ m ={⊤}[∅]▷=∗^n P) →
  ⊢ P.
Proof.
  intros Hiter.
  eapply (fupd_soundness_lc (m + n) ⊤ ⊤); [apply _..|].
  iIntros (Hinv) "Hlc". rewrite lc_split.
  iDestruct "Hlc" as "[Hm Hn]". iPoseProof (Hiter with "Hm") as "Hupd".
  clear Hiter.
  (* FIXME can we reuse [step_fupdN_soundness_lc] instead of redoing the induction? *)
  iInduction n as [|n] "IH"; simpl.
  - by iModIntro.
  - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]".
    iMod "Hupd". iMod (lc_fupd_elim_later with "Hone Hupd") as "> Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.

(** Generic soundness lemma for the fancy update, parameterized by [use_credits]
  on whether to use credits or not. *)
Lemma step_fupdN_soundness_gen `{!invGpreS Σ} (P : iProp Σ) `{!Plain P}
  (hlc : has_lc) (n m : nat) :
  (∀ `{Hinv : invGS_gen hlc Σ},
    £ m ={⊤,∅}=∗ |={∅}▷=>^n P) →
  ⊢ P.
Proof.
  destruct hlc.
  - apply step_fupdN_soundness_lc. done.
  - apply step_fupdN_soundness_no_lc. done.
Qed.

(** More flexible soundness theorem *)
Definition fupd_finally_def `{!invGS_gen HasLc Σ}
    (E : coPset) (P : iProp Σ) : iProp Σ :=
  wsat -∗ ownE E -∗ |==£|> P.
Local Definition fupd_finally_aux : seal (@fupd_finally_def).
Proof. by eexists. Qed.
Local Definition fupd_finally := fupd_finally_aux.(unseal).
Local Definition fupd_finally_unseal :
  @fupd_finally = @fupd_finally_def := fupd_finally_aux.(seal_eq).
Global Arguments fupd_finally {Σ _}.

Notation "|={ E |}=> Q" := (fupd_finally E Q)
  (at level 20, E at level 50, Q at level 200,
   format "'[  ' |={ E |}=>  '/' Q ']'") : bi_scope.
Notation "P ={ E |}=∗ Q" := (P -∗ fupd_finally E Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "'[' P  ={ E |}=∗  '/' '[' Q ']' ']'") : bi_scope.
Notation "P ={ E |}=∗ Q" := (P -∗ fupd_finally E Q)
  (at level 99, E at level 50, Q at level 200,
   format "'[' P  ={ E |}=∗  '/' '[' Q ']' ']'") : stdpp_scope.

Section fupd_finally.
  Context `{!invGS_gen HasLc Σ}.

  Global Instance fupd_finally_ne E : NonExpansive (fupd_finally E).
  Proof. rewrite fupd_finally_unseal. solve_proper. Qed.

  Lemma fupd_finally_mono E P Q : (P ⊢ Q) → (|={E|}=> P) ⊢ (|={E|}=> Q).
  Proof. rewrite fupd_finally_unseal. solve_proper. Qed.

  Lemma fupd_finally_intro E P : ■ P ⊢ |={E|}=> P.
  Proof.
    rewrite fupd_finally_unseal.
    iIntros "#HP _ _". by iApply le_upd_finally_intro.
  Qed.

  Lemma fupd_fupd_finally E1 E2 P : (|={E1,E2}=> |={E2|}=> P) ⊢ |={E1|}=> P.
  Proof.
    rewrite fupd_finally_unseal uPred_fupd_unseal.
    iIntros "HP Hw HE1". rewrite /uPred_fupd_def /=.
    iApply le_upd_le_upd_finally.
    iMod ("HP" with "[$Hw $HE1]") as "HP"; iModIntro.
    iApply except_0_le_upd_finally. iMod "HP"; iModIntro.
    iDestruct "HP" as "(Hw & HE2 & HP)". iApply ("HP" with "Hw HE2").
  Qed.

  Lemma fupd_finally_later E P : (£ 1 -∗ |={E|}=> P) ⊢ |={E|}=> ▷ ◇ P.
  Proof.
    rewrite fupd_finally_unseal. iIntros "H Hw HE". iApply le_upd_finally_later.
    iIntros "H£". iApply ("H" with "H£ Hw HE").
  Qed.

  Lemma fupd_finally_keep E P Q `{!Timeless P} :
    (|={E|}=> P) ∧ (P -∗ |={E|}=> Q) ⊢ |={E|}=> Q.
  Proof.
    rewrite fupd_finally_unseal. iIntros "H Hw HE".
    iApply (le_upd_finally_keep P). iSplit.
    - iDestruct "H" as "[H _]". iApply ("H" with "Hw HE").
    - iIntros "HP". iDestruct "H" as "[_ H]". iApply ("H" with "HP Hw HE").
  Qed.

  Lemma fupd_finally_forall {A} E (Φ : A → iProp Σ) :
    (∀ x, |={E|}=> Φ x) ⊢ |={E|}=> ∀ x, Φ x.
  Proof.
    rewrite fupd_finally_unseal. iIntros "H Hw HE".
    iApply le_upd_finally_forall; iIntros (x). iApply ("H" with "Hw HE").
  Qed.

  (* Derived *)
  Global Instance fupd_finally_proper E : Proper ((⊣⊢) ==> (⊣⊢)) (fupd_finally E).
  Proof. apply: ne_proper. Qed.
  Global Instance fupd_finally_mono' E : Proper ((⊢) ==> (⊢)) (fupd_finally E).
  Proof. intros P Q. apply fupd_finally_mono. Qed.
  Global Instance fupd_finally_flip_mono' E :
    Proper (flip (⊢) ==> flip (⊢)) (fupd_finally E).
  Proof. intros P Q. apply fupd_finally_mono. Qed.

  Lemma fupd_finally_and E P Q : (|={E|}=> P) ∧ (|={E|}=> Q) ⊢ |={E|}=> P ∧ Q.
  Proof. rewrite !and_alt -fupd_finally_forall. by f_equiv=> -[]. Qed.
  Lemma fupd_finally_wand E P Q : (|={E|}=> P) -∗ ■ (P -∗ Q) -∗ (|={E|}=> Q).
  Proof.
    apply entails_wand, wand_intro_r.
    rewrite -plainly_and_sep_r -plainly_idemp.
    rewrite (fupd_finally_intro E) fupd_finally_and.
    by rewrite plainly_and_sep_r plainly_elim wand_elim_r.
  Qed.

  Lemma fupd_finally_mask_mono E1 E2 P : E1 ⊆ E2 → (|={E1|}=> P) ⊢ |={E2|}=> P.
  Proof.
    iIntros (?) "H". iApply fupd_fupd_finally. by iApply fupd_mask_intro_discard.
  Qed.

  Global Instance from_pure_fupd_finally a E P φ :
    FromPure a P φ → FromPure a (|={E|}=> P) φ.
  Proof.
    rewrite /FromPure=> <-. rewrite -fupd_finally_intro.
    by apply plainly_intro; [destruct a; simpl; apply _|].
  Qed.

  Global Instance from_forall_fupd_finally E {A} P (Φ : A → iProp Σ) name :
    FromForall P Φ name →
    FromForall (|={E|}=> P) (λ a, |={E|}=> (Φ a))%I name.
  Proof. rewrite /FromForall=> <-. apply fupd_finally_forall. Qed.

  Global Instance is_except_0_fupd_finally E P : IsExcept0 (|={E|}=> P).
  Proof.
    by rewrite /IsExcept0 -{2}(fupd_fupd_finally E E) -except_0_fupd -fupd_intro.
  Qed.

  Global Instance elim_modal_bupd_fupd_finally p E P Q :
    ElimModal True p false (|==> P) P (|={E|}=> Q) (|={E|}=> Q).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim /= bupd_frame_r wand_elim_r.
    by rewrite (bupd_fupd E) fupd_fupd_finally.
  Qed.
  Global Instance elim_modal_fupd_fupd_finally p E1 E2 P Q :
    ElimModal True p false (|={E1,E2}=> P) P (|={E1|}=> Q) (|={E2|}=> Q).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim /= fupd_frame_r wand_elim_r.
    by rewrite fupd_fupd_finally.
  Qed.
End fupd_finally.

Lemma fupd_finally_soundness `{!invGpreS Σ} n E P :
  (∀ `{!invGS_gen HasLc Σ}, £ n ⊢ |={E|}=> P) → ⊢ P.
Proof.
  rewrite fupd_finally_unseal=> HP.
  apply (le_upd_finally_soundness n); iIntros (?) "H£".
  iApply le_upd_le_upd_finally. iMod wsat_alloc as (Hw) "[Hw HE]". iModIntro.
  iApply (HP (InvG _ _ _ _) with "H£ Hw").
  rewrite (union_difference_L E ⊤); [|set_solver].
  rewrite ownE_op; [|set_solver]. iDestruct "HE" as "[$ _]".
Qed.

(** * Now the Rocq-level tactic [iNext credit:H] *)
Lemma tac_lc_add_laterN_split `{!invGS_gen HasLc Σ} Δ Δ' Δ'' E i n m m' P :
  envs_lookup i Δ = Some (false, £ m) →
  (* Ensure that the goal [P] that be turned into a [fupd], i.e. the goal is a
  WP or a (possibly mask-changing) fancy update *)
  AddModal (|={E}=> P) P P →
  NatCancel m n m' 0 →
  envs_replace i false false (Esnoc Enil i (£ m')) Δ = Some Δ' →
  MaybeIntoLaterNEnvs n Δ' Δ'' →
  (m' = 0 ∧
   match envs_lookup_delete false i Δ'' with
   | Some (_, _, Δ''') => envs_entails Δ''' P
   | None => False
   end
   ∨ envs_entails Δ'' P) →
  envs_entails Δ P.
Proof.
  rewrite envs_entails_unseal /NatCancel /AddModal right_id.
  intros Hi HP <- HΔ HΔ' HΔ''. rewrite -HP -wand_refl right_id.
  rewrite envs_replace_sound //. simpl.
  rewrite Nat.add_comm lc_split. rewrite right_id -assoc wand_elim_r.
  rewrite into_laterN_env_sound.
  destruct HΔ'' as [[-> HΔ'']|<-].
  - destruct (envs_lookup_delete _ _) as [[[p Pi] Δ''']|] eqn:HΔ'''; [|done].
    rewrite envs_lookup_delete_sound // HΔ''.
    iIntros "[H£ [_ H]]".
    iApply (lc_fupd_add_laterN with "H£"). by iIntros "!> !>".
  - iIntros "[H£ H]". iApply (lc_fupd_add_laterN with "H£"). by iIntros "!> !>".
Qed.

Tactic Notation "iNext" open_constr(n) "credit:" constr(H) :=
  iStartProof;
  notypeclasses refine (tac_lc_add_laterN_split _ _ _ _ H n _ _ _ _ _ _ _ _ _);
    [(* look up the later credit named H *)
     pm_reflexivity ||
     fail "iNext:" H "is not a later credit"
    |(* AddModal *)
     tc_solve ||
     fail "iNext: The goal cannot be turned into a fancy update modality"
    |(* NatCancel *)
     tc_solve ||
     fail "iNext:" H " does not contain" n "credits"
    |(* envs_replace *)
     pm_reflexivity
    |(* MaybeIntoLaterNEnvs *)
     tc_solve
    |pm_reduce; pm_prettify; first
       [left; split; [done|] (* credit is used up *)
       |right (* credit has the residue *)
       ]
    ].
Tactic Notation "iNext" "credit:" constr(H) := iNext 1 credit: H.
