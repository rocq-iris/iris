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
  iIntros "[$ $]". iApply (lc_le_upd_elim_later with "Hf").
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

(** Flexible soundness theorem through "finally" modality *)
(** The [fupd_finally] modality allows convenient proofs of soundness/adequacy
of a custom modality/program logic. To use it, perform the following steps:
- Apply [pure_soundness] to turn your pure goal into an Iris entailment.
- (Only when *not* using later credits ([HasNoLc]), or proving a theorem generic
  in [hlc : has_lc])
  Apply [laterN_soundness] to add a number of laters.
- Apply [fupd_finally_soundness] to turn the goal into [|={E|}=> ..] and to
  allocate a number of later credits. In addition to the later credits you want
  to supply to the user, you also want to allocate enough later credits to
  eliminate the laters obtained from unfolding a recursive definition (such as
  WP) sufficiently many times.

Next, you can:
- Eliminate update modalities around [|={E|}=> ..] through [fupd_fupd_finally].
  This lemma is used implicitly when using the [iMod] tactic.
- "Duplicate" the context for proving timeless assertions through
  [fupd_finally_keep].
- Introduce foralls below [|={E|}=> ..] through [fupd_finally_forall]. This
  lemma is used implicitly when using the [iIntros] tactic.
- Turn laters below [|={E|}=> ..] into later credits through [fupd_finally_lc]
  or commute them out through [fupd_finally_later].
- Finally introduce the modality using [fupd_finally_intro].

See the proofs of the derived soundness theorems below for examples on how to
use the modality. Also see the proofs of adequacy of WP or total WP. *)
Definition fupd_finally_def `{!invGS_gen hlc Σ}
    (E : coPset) (P : iProp Σ) : iProp Σ :=
  wsat -∗ ownE E -∗ |==£|> P.
Local Definition fupd_finally_aux : seal (@fupd_finally_def).
Proof. by eexists. Qed.
Local Definition fupd_finally := fupd_finally_aux.(unseal).
Local Definition fupd_finally_unseal :
  @fupd_finally = @fupd_finally_def := fupd_finally_aux.(seal_eq).
Global Arguments fupd_finally {hlc Σ _}.

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
  Context `{!invGS_gen hlc Σ}.

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
    iMod (le_upd_if_into_le_upd with "(HP [$Hw $HE1])") as "HP"; iModIntro.
    iApply except_0_le_upd_finally. iMod "HP"; iModIntro.
    iDestruct "HP" as "(Hw & HE2 & HP)". iApply ("HP" with "Hw HE2").
  Qed.

  (** Generate a later credit by removing a later below the modality. This only
  works if the proposition below the later can be turned into an except-0 [◇]. *)
  Lemma fupd_finally_lc E P : (£ 1 -∗ |={E|}=> P) ⊢ |={E|}=> ▷ ◇ P.
  Proof.
    rewrite fupd_finally_unseal. iIntros "H Hw HE". iApply le_upd_finally_lc.
    iIntros "H£". iApply ("H" with "H£ Hw HE").
  Qed.

  Lemma fupd_finally_except_0 E P : (|={E|}=> ◇ P) ⊢ |={E|}=> P.
  Proof.
    rewrite fupd_finally_unseal. iIntros "H Hw HE".
    iApply le_upd_finally_except_0. iApply ("H" with "Hw HE").
  Qed.

  (** Commute a later out of the modality. This only works if the proposition
  below the later can be turned into an except-0 [◇].
  This lemma is derivable from [fupd_finally_lc] with [hlc:=HasLc], but
  not with [hlc:=HasNoLc]. *)
  Lemma fupd_finally_later E P : ▷ (|={E|}=> P) ⊢ |={E|}=> ▷ ◇ P.
  Proof.
    rewrite fupd_finally_unseal. iIntros "H Hw HE". iApply le_upd_finally_later.
    iNext. iApply ("H" with "Hw HE").
  Qed.

  (* [iApply] this lemma to use your current context for proving a timeless
  assertion [P] *without* actually using up the context. You can then continue
  the proof in the second conjunct. *)
  Lemma fupd_finally_keep {E} P Q `{!Timeless P} :
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

  Lemma step_fupdN_fupd_finally E1 E2 n P :
    (|={E1}[E2]▷=>^n |={E1|}=> P) ⊢ |={E1|}=> ▷^n ◇ P.
  Proof.
    iIntros "HP". iInduction n as [|n] "IH"; simpl.
    { by iEval (rewrite -except_0_intro). }
    iMod "HP". iEval (rewrite -except_0_idemp -except_0_laterN).
    iApply fupd_finally_later; iNext. iMod "HP". by iApply "IH".
  Qed.
End fupd_finally.

Lemma fupd_finally_soundness hlc `{!invGpreS Σ} n E P :
  (∀ `{!invGS_gen hlc Σ}, £ n ⊢ |={E|}=> P) → ⊢ P.
Proof.
  rewrite fupd_finally_unseal=> HP.
  apply (le_upd_finally_soundness n); iIntros (?) "H£".
  iApply le_upd_le_upd_finally. iMod wsat_alloc as (Hw) "[Hw HE]". iModIntro.
  iApply (HP (InvG _ _ _ _) with "H£ Hw").
  rewrite (union_difference_L E ⊤); [|set_solver].
  rewrite ownE_op; [|set_solver]. iDestruct "HE" as "[$ _]".
Qed.

(** Derived soundness theorems *)
(** Note: the [hlc = HasNoLc] versions also allow generating later credits, but
these cannot be used for anything. They are merely provided to enable making
the adequacy proof generic in whether later credits are used. *)
Lemma fupd_soundness hlc `{!invGpreS Σ} n E1 E2 (P : iProp Σ) `{!Plain P} :
  (∀ `{invGS_gen hlc Σ}, £ n ={E1,E2}=∗ P) →
  ⊢ P.
Proof.
  intros HP. apply (fupd_finally_soundness hlc n E1); iIntros (?) "H£".
  iMod (HP with "H£"). iApply fupd_finally_intro. by iApply plain_plainly.
Qed.

Lemma step_fupdN_soundness hlc `{!invGpreS Σ} n m (P : iProp Σ) `{!Plain P} :
  (∀ `{!invGS_gen hlc Σ}, £ m ={⊤,∅}=∗ |={∅}▷=>^n P) →
  ⊢ P.
Proof.
  intros HP. apply (laterN_soundness _  (n + 1)); simpl.
  apply (fupd_finally_soundness hlc m ⊤); iIntros (Hinv) "Hc".
  iMod (HP with "Hc") as "HP".
  rewrite laterN_add /= -except_0_into_later. iApply step_fupdN_fupd_finally.
  iApply (step_fupdN_wand with "HP"); iIntros "HP".
  iApply fupd_finally_intro. by iApply plain_plainly.
Qed.

Lemma step_fupdN_soundness' hlc `{!invGpreS Σ} n m (P : iProp Σ) `{!Plain P} :
  (∀ `{!invGS_gen hlc Σ}, £ m ={⊤}[∅]▷=∗^n P) →
  ⊢ P.
Proof.
  intros HP. apply (laterN_soundness _  (n + 1)); simpl.
  apply (fupd_finally_soundness hlc m ⊤); iIntros (Hinv) "Hc".
  iPoseProof (HP with "Hc") as "HP".
  rewrite laterN_add /= -except_0_into_later. iApply step_fupdN_fupd_finally.
  iApply (step_fupdN_wand with "HP"); iIntros "HP".
  iApply fupd_finally_intro. by iApply plain_plainly.
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
