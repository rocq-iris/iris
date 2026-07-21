From iris.bi Require Export monpred.
From iris.bi Require Import plainly.
From iris.proofmode Require Import proofmode classes_make modality_instances.

Class MakeMonPredAt {I : biIndex} {PROP : bi} (i : I)
      (P : monPred I PROP) (𝓟 : PROP) :=
  make_monPred_at : P i ⊣⊢ 𝓟.
Global Arguments MakeMonPredAt {_ _} _ _%_I _%_I.
(** Since [MakeMonPredAt] is used by [AsEmpValid] to import lemmas into the
proof mode, the index [I] and BI [PROP] often contain evars. Hence, it is
important to use the mode [!] also for the first two arguments. *)
Global Hint Mode MakeMonPredAt ! ! - ! - : typeclass_instances.

Class IsBiIndexRel {I : biIndex} (i j : I) := is_bi_index_rel : i ⊑ j.
Global Hint Mode IsBiIndexRel + - - : typeclass_instances.
Global Instance is_bi_index_rel_refl {I : biIndex} (i : I) : IsBiIndexRel i i | 0.
Proof. by rewrite /IsBiIndexRel. Qed.
Global Hint Extern 1 (IsBiIndexRel _ _) => unfold IsBiIndexRel; assumption
            : typeclass_instances.

(** Frame [𝓡] into the goal [monPred_at P i] and determine the remainder [𝓠].
    Used when framing encounters a monPred_at in the goal. *)
Class FrameMonPredAt {I : biIndex} {PROP : bi} (p : bool) (i : I)
      (𝓡 : PROP) (P : monPred I PROP) (𝓠 : PROP) :=
  frame_monPred_at : □?p 𝓡 ∗ 𝓠 ⊢ P i.
Global Arguments FrameMonPredAt {_ _} _ _ _%_I _%_I _%_I.
Global Hint Mode FrameMonPredAt + + + - ! ! - : typeclass_instances.

Section modalities.
  Context {I : biIndex} {PROP : bi}.

  Lemma modality_objectively_mixin :
    modality_mixin (@monPred_objectively I PROP)
      (MIEnvFilter Objective) (MIEnvFilter Objective).
  Proof.
    split; simpl; split_and?; intros;
      try select (TCDiag _ _ _) (fun H => destruct H);
      eauto using bi.equiv_entails_1_2, objective_objectively,
        monPred_objectively_mono, monPred_objectively_and,
        monPred_objectively_sep_2 with typeclass_instances.
  Qed.
  Definition modality_objectively :=
    Modality _ modality_objectively_mixin.
End modalities.

Section bi.
Context {I : biIndex} {PROP : bi}.
Local Notation monPredI := (monPredI I PROP).
Local Notation monPred := (monPred I PROP).
Local Notation MakeMonPredAt := (@MakeMonPredAt I PROP).
Implicit Types P Q R : monPred.
Implicit Types 𝓟 𝓠 𝓡 : PROP.
Implicit Types φ : Prop.
Implicit Types i j : I.

Global Instance from_modal_objectively P :
  FromModal True modality_objectively (<obj> P) (<obj> P) P | 1.
Proof. by rewrite /FromModal. Qed.
Global Instance from_modal_subjectively P :
  FromModal True modality_id (<subj> P) (<subj> P) P | 1.
Proof. by rewrite /FromModal /= -monPred_subjectively_intro. Qed.

Global Instance from_modal_affinely_monPred_at φ `(sel : A) P Q 𝓠 i :
  FromModal φ modality_affinely sel P Q →
  MakeMonPredAt i Q 𝓠 →
  FromModal φ modality_affinely sel (P i) 𝓠 | 0.
Proof.
  rewrite /FromModal /MakeMonPredAt /==> HPQ <- ?.
  by rewrite -HPQ // monPred_at_affinely.
Qed.
Global Instance from_modal_persistently_monPred_at φ `(sel : A) P Q 𝓠 i :
  FromModal φ modality_persistently sel P Q →
  MakeMonPredAt i Q 𝓠 →
  FromModal φ modality_persistently sel (P i) 𝓠 | 0.
Proof.
  rewrite /FromModal /MakeMonPredAt /==> HPQ <- ?.
  by rewrite -HPQ // monPred_at_persistently.
Qed.
Global Instance from_modal_intuitionistically_monPred_at φ `(sel : A) P Q 𝓠 i :
  FromModal φ modality_intuitionistically sel P Q →
  MakeMonPredAt i Q 𝓠 →
  FromModal φ modality_intuitionistically sel (P i) 𝓠 | 0.
Proof.
  rewrite /FromModal /MakeMonPredAt /==> HPQ <- ?.
  by rewrite -HPQ // monPred_at_affinely monPred_at_persistently.
Qed.
Global Instance from_modal_id_monPred_at φ `(sel : A) P Q 𝓠 i :
  FromModal φ modality_id sel P Q → MakeMonPredAt i Q 𝓠 →
  FromModal φ modality_id sel (P i) 𝓠.
Proof. rewrite /FromModal /MakeMonPredAt=> HPQ <- ?. by rewrite -HPQ. Qed.

Global Instance make_monPred_at_pure φ i : MakeMonPredAt i ⌜φ⌝ ⌜φ⌝.
Proof. by rewrite /MakeMonPredAt monPred_at_pure. Qed.
Global Instance make_monPred_at_emp i : MakeMonPredAt i emp emp.
Proof. by rewrite /MakeMonPredAt monPred_at_emp. Qed.
Global Instance make_monPred_at_sep i P 𝓟 Q 𝓠 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  MakeMonPredAt i (P ∗ Q) (𝓟 ∗ 𝓠).
Proof. by rewrite /MakeMonPredAt monPred_at_sep=><-<-. Qed.
Global Instance make_monPred_at_and i P 𝓟 Q 𝓠 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  MakeMonPredAt i (P ∧ Q) (𝓟 ∧ 𝓠).
Proof. by rewrite /MakeMonPredAt monPred_at_and=><-<-. Qed.
Global Instance make_monPred_at_or i P 𝓟 Q 𝓠 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  MakeMonPredAt i (P ∨ Q) (𝓟 ∨ 𝓠).
Proof. by rewrite /MakeMonPredAt monPred_at_or=><-<-. Qed.
Global Instance make_monPred_at_forall {A} i (Φ : A → monPred) (Ψ : A → PROP) :
  (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → MakeMonPredAt i (∀ a, Φ a) (∀ a, Ψ a).
Proof. rewrite /MakeMonPredAt monPred_at_forall=>H. by setoid_rewrite <- H. Qed.
Global Instance make_monPred_at_exists {A} i (Φ : A → monPred) (Ψ : A → PROP) :
  (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → MakeMonPredAt i (∃ a, Φ a) (∃ a, Ψ a).
Proof. rewrite /MakeMonPredAt monPred_at_exist=>H. by setoid_rewrite <- H. Qed.
Global Instance make_monPred_at_persistently i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (<pers> P) (<pers> 𝓟).
Proof. by rewrite /MakeMonPredAt monPred_at_persistently=><-. Qed.
Global Instance make_monPred_at_affinely i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (<affine> P) (<affine> 𝓟).
Proof. by rewrite /MakeMonPredAt monPred_at_affinely=><-. Qed.
Global Instance make_monPred_at_intuitionistically i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (□ P) (□ 𝓟).
Proof. by rewrite /MakeMonPredAt monPred_at_intuitionistically=><-. Qed.
Global Instance make_monPred_at_absorbingly i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (<absorb> P) (<absorb> 𝓟).
Proof. by rewrite /MakeMonPredAt monPred_at_absorbingly=><-. Qed.
Global Instance make_monPred_at_persistently_if i P 𝓟 p :
  MakeMonPredAt i P 𝓟 →
  MakeMonPredAt i (<pers>?p P) (<pers>?p 𝓟).
Proof. destruct p; simpl; apply _. Qed.
Global Instance make_monPred_at_affinely_if i P 𝓟 p :
  MakeMonPredAt i P 𝓟 →
  MakeMonPredAt i (<affine>?p P) (<affine>?p 𝓟).
Proof. destruct p; simpl; apply _. Qed.
Global Instance make_monPred_at_absorbingly_if i P 𝓟 p :
  MakeMonPredAt i P 𝓟 →
  MakeMonPredAt i (<absorb>?p P) (<absorb>?p 𝓟).
Proof. destruct p; simpl; apply _. Qed.
Global Instance make_monPred_at_intuitionistically_if i P 𝓟 p :
  MakeMonPredAt i P 𝓟 →
  MakeMonPredAt i (□?p P) (□?p 𝓟).
Proof. destruct p; simpl; apply _. Qed.
Global Instance make_monPred_at_embed i 𝓟 : MakeMonPredAt i ⎡𝓟⎤ 𝓟.
Proof. by rewrite /MakeMonPredAt monPred_at_embed. Qed.
Global Instance make_monPred_at_in i j : MakeMonPredAt j (monPred_in i) ⌜i ⊑ j⌝.
Proof. by rewrite /MakeMonPredAt monPred_at_in. Qed.
Global Instance make_monPred_at_default i P : MakeMonPredAt i P (P i) | 100.
Proof. by rewrite /MakeMonPredAt. Qed.
Global Instance make_monPred_at_bupd `{!BiBUpd PROP} i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (|==> P) (|==> 𝓟).
Proof. by rewrite /MakeMonPredAt monPred_at_bupd=> <-. Qed.

Global Instance from_assumption_make_monPred_at_l p i j P 𝓟 :
  MakeMonPredAt i P 𝓟 → IsBiIndexRel j i → KnownLFromAssumption p (P j) 𝓟.
Proof.
  rewrite /MakeMonPredAt /KnownLFromAssumption /FromAssumption /IsBiIndexRel=><- ->.
  apply  bi.intuitionistically_if_elim.
Qed.
Global Instance from_assumption_make_monPred_at_r p i j P 𝓟 :
  MakeMonPredAt i P 𝓟 → IsBiIndexRel i j → KnownRFromAssumption p 𝓟 (P j).
Proof.
  rewrite /MakeMonPredAt /KnownRFromAssumption /FromAssumption /IsBiIndexRel=><- ->.
  apply  bi.intuitionistically_if_elim.
Qed.

Global Instance from_assumption_make_monPred_objectively p P Q :
  FromAssumption p P Q → KnownLFromAssumption p (<obj> P) Q.
Proof.
  by rewrite /KnownLFromAssumption /FromAssumption monPred_objectively_elim.
Qed.
Global Instance from_assumption_make_monPred_subjectively p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (<subj> Q).
Proof.
  by rewrite /KnownRFromAssumption /FromAssumption -monPred_subjectively_intro.
Qed.

Global Instance as_emp_valid_monPred_at d φ P (Φ : I → PROP) :
  AsEmpValid0 d φ P →
  (∀ i, MakeMonPredAt i P (Φ i)) →
  AsEmpValid d φ (∀ i, Φ i) | 100.
Proof.
  rewrite /MakeMonPredAt /AsEmpValid0 /AsEmpValid /bi_emp_valid=> -[He1 He2] EQ.
  setoid_rewrite <-EQ. split.
  - move=>? /He1[//|H]. apply bi.forall_intro=>i. rewrite -H. by rewrite monPred_at_emp.
  - move=>? HP. apply He2 => //. split=>i. rewrite monPred_at_emp HP bi.forall_elim //.
Qed.
Global Instance as_emp_valid_monPred_at_wand d φ P Q (Φ Ψ : I → PROP) :
  AsEmpValid0 d φ (P -∗ Q) →
  (∀ i, MakeMonPredAt i P (Φ i)) → (∀ i, MakeMonPredAt i Q (Ψ i)) →
  AsEmpValid d φ (∀ i, Φ i -∗ Ψ i).
Proof.
  rewrite /AsEmpValid0 /AsEmpValid /MakeMonPredAt. intros [He1 He2] EQ1 EQ2.
  setoid_rewrite <-EQ1. setoid_rewrite <-EQ2. split.
  - move=>? /He1/bi.wand_entails HP. setoid_rewrite HP => //. by iIntros (i) "$".
  - move=>? HP. apply He2 => //. apply bi.entails_wand.
    split=>i. iIntros "H". by iApply HP.
Qed.
Global Instance as_emp_valid_monPred_at_equiv d φ P Q (Φ Ψ : I → PROP) :
  AsEmpValid0 d φ (P ∗-∗ Q) →
  (∀ i, MakeMonPredAt i P (Φ i)) → (∀ i, MakeMonPredAt i Q (Ψ i)) →
  AsEmpValid d φ (∀ i, Φ i ∗-∗ Ψ i).
Proof.
  rewrite /AsEmpValid0 /AsEmpValid /MakeMonPredAt. intros [He1 He2] EQ1 EQ2.
  setoid_rewrite <-EQ1. setoid_rewrite <-EQ2. split.
  - move=>? /He1 /bi.wand_iff_equiv HP. setoid_rewrite HP => //.
    iIntros. iSplit; iIntros "$".
  - move=>? HP. apply He2 => //. apply bi.equiv_wand_iff.
    split=>i. by iSplit; iIntros; iApply HP.
Qed.

Global Instance into_pure_monPred_at P φ i : IntoPure P φ → IntoPure (P i) φ.
Proof. rewrite /IntoPure=>->. by rewrite monPred_at_pure. Qed.
Global Instance from_pure_monPred_at a P φ i : FromPure a P φ → FromPure a (P i) φ.
Proof. rewrite /FromPure=><-. by rewrite monPred_at_affinely_if monPred_at_pure. Qed.
Global Instance into_pure_monPred_in i j : @IntoPure PROP (monPred_in i j) (i ⊑ j).
Proof. by rewrite /IntoPure monPred_at_in. Qed.
Global Instance from_pure_monPred_in i j : @FromPure PROP false (monPred_in i j) (i ⊑ j).
Proof. by rewrite /FromPure monPred_at_in. Qed.

Global Instance into_persistent_monPred_at p P Q 𝓠 i :
  IntoPersistent p P Q → MakeMonPredAt i Q 𝓠 → IntoPersistent p (P i) 𝓠 | 0.
Proof.
  rewrite /IntoPersistent /MakeMonPredAt  =>-[/(_ i) ?] <-.
  by rewrite -monPred_at_persistently -monPred_at_persistently_if.
Qed.

Lemma into_wand_monPred_at_unknown_unknown p q R P 𝓟 Q 𝓠 i :
  IntoWand p q R P Q → MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  IntoWand p q (R i) 𝓟 𝓠.
Proof.
  rewrite /IntoWand /MakeMonPredAt /bi_affinely_if /bi_persistently_if.
  destruct p, q=> /bi.wand_elim_l' [/(_ i) H] <- <-; apply bi.wand_intro_r;
  revert H; by rewrite monPred_at_sep ?monPred_at_affinely ?monPred_at_persistently.
Qed.
Lemma into_wand_monPred_at_unknown_known p q R P 𝓟 Q i j :
  IsBiIndexRel i j → IntoWand p q R P Q →
  MakeMonPredAt j P 𝓟 → IntoWand p q (R i) 𝓟 (Q j).
Proof.
  rewrite /IntoWand /IsBiIndexRel /MakeMonPredAt=>-> ? ?.
  eapply into_wand_monPred_at_unknown_unknown=>//. apply _.
Qed.
Lemma into_wand_monPred_at_known_unknown_le p q R P Q 𝓠 i j :
  IsBiIndexRel i j → IntoWand p q R P Q →
  MakeMonPredAt j Q 𝓠 → IntoWand p q (R i) (P j) 𝓠.
Proof.
  rewrite /IntoWand /IsBiIndexRel /MakeMonPredAt=>-> ? ?.
  eapply into_wand_monPred_at_unknown_unknown=>//. apply _.
Qed.
Lemma into_wand_monPred_at_known_unknown_ge p q R P Q 𝓠 i j :
  IsBiIndexRel i j → IntoWand p q R P Q →
  MakeMonPredAt j Q 𝓠 → IntoWand p q (R j) (P i) 𝓠.
Proof.
  rewrite /IntoWand /IsBiIndexRel /MakeMonPredAt=>-> ? ?.
  eapply into_wand_monPred_at_unknown_unknown=>//. apply _.
Qed.

Global Instance into_wand_wand'_monPred p q P Q 𝓟 𝓠 i :
  IntoWand' p q ((P -∗ Q) i) 𝓟 𝓠 → IntoWand p q ((P -∗ Q) i) 𝓟 𝓠 | 100.
Proof. done. Qed.
Global Instance into_wand_impl'_monPred p q P Q 𝓟 𝓠 i :
  IntoWand' p q ((P → Q) i) 𝓟 𝓠 → IntoWand p q ((P → Q) i) 𝓟 𝓠 | 100.
Proof. done. Qed.

Global Instance from_forall_monPred_at_wand P Q (Φ Ψ : I → PROP) i :
  (∀ j, MakeMonPredAt j P (Φ j)) → (∀ j, MakeMonPredAt j Q (Ψ j)) →
  FromForall ((P -∗ Q) i)%I (λ j, ⌜i ⊑ j⌝ → Φ j -∗ Ψ j)%I (to_ident_name idx).
Proof.
  rewrite /FromForall /MakeMonPredAt monPred_at_wand=> H1 H2. do 2 f_equiv.
  by rewrite H1 H2.
Qed.
Global Instance from_forall_monPred_at_impl P Q (Φ Ψ : I → PROP) i :
  (∀ j, MakeMonPredAt j P (Φ j)) → (∀ j, MakeMonPredAt j Q (Ψ j)) →
  FromForall ((P → Q) i)%I (λ j, ⌜i ⊑ j⌝ → Φ j → Ψ j)%I (to_ident_name idx).
Proof.
  rewrite /FromForall /MakeMonPredAt monPred_at_impl=> H1 H2. do 2 f_equiv.
  by rewrite H1 H2 bi.pure_impl_forall.
Qed.

Global Instance into_forall_monPred_at_index P i :
  IntoForall (P i) (λ j, ⌜i ⊑ j⌝ → P j)%I | 100.
Proof.
  rewrite /IntoForall. setoid_rewrite bi.pure_impl_forall.
  do 2 apply bi.forall_intro=>?. by f_equiv.
Qed.

Global Instance from_and_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  FromAnd P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  FromAnd (P i) 𝓠1 𝓠2.
Proof.
  rewrite /FromAnd /MakeMonPredAt /MakeMonPredAt=> <- <- <-.
  by rewrite monPred_at_and.
Qed.
Global Instance into_and_monPred_at p P Q1 𝓠1 Q2 𝓠2 i :
  IntoAnd p P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  IntoAnd p (P i) 𝓠1 𝓠2.
Proof.
  rewrite /IntoAnd /MakeMonPredAt /bi_affinely_if /bi_persistently_if.
  destruct p=>-[/(_ i) H] <- <-; revert H;
  by rewrite ?monPred_at_affinely ?monPred_at_persistently monPred_at_and.
Qed.

Global Instance from_sep_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  FromSep P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  FromSep (P i) 𝓠1 𝓠2.
Proof. rewrite /FromSep /MakeMonPredAt=> <- <- <-. by rewrite monPred_at_sep. Qed.
Global Instance into_sep_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  IntoSep P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  IntoSep (P i) 𝓠1 𝓠2.
Proof. rewrite /IntoSep /MakeMonPredAt=> -> <- <-. by rewrite monPred_at_sep. Qed.
Global Instance from_or_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  FromOr P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  FromOr (P i) 𝓠1 𝓠2.
Proof. rewrite /FromOr /MakeMonPredAt=> <- <- <-. by rewrite monPred_at_or. Qed.
Global Instance into_or_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  IntoOr P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  IntoOr (P i) 𝓠1 𝓠2.
Proof. rewrite /IntoOr /MakeMonPredAt=> -> <- <-. by rewrite monPred_at_or. Qed.

Global Instance from_exist_monPred_at {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  FromExist P Φ → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → FromExist (P i) Ψ.
Proof.
  rewrite /FromExist /MakeMonPredAt=><- H. setoid_rewrite <- H.
  by rewrite monPred_at_exist.
Qed.
Global Instance into_exist_monPred_at {A} P (Φ : A → monPred) name (Ψ : A → PROP) i :
  IntoExist P Φ name → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → IntoExist (P i) Ψ name.
Proof.
  rewrite /IntoExist /MakeMonPredAt=>-> H. setoid_rewrite <- H.
  by rewrite monPred_at_exist.
Qed.

Global Instance from_forall_monPred_at_objectively P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → FromForall ((<obj> P) i)%I Φ (to_ident_name idx).
Proof.
  rewrite /FromForall /MakeMonPredAt monPred_at_objectively=>H. by setoid_rewrite <- H.
Qed.
Global Instance into_forall_monPred_at_objectively P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → IntoForall ((<obj> P) i) Φ.
Proof.
  rewrite /IntoForall /MakeMonPredAt monPred_at_objectively=>H. by setoid_rewrite <- H.
Qed.

Global Instance from_exist_monPred_at_ex P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → FromExist ((<subj> P) i) Φ.
Proof.
  rewrite /FromExist /MakeMonPredAt monPred_at_subjectively=>H. by setoid_rewrite <- H.
Qed.
(* TODO: this implementation uses [idx] as the automatic name for the index. In
theory a monPred could define an appropriate metavariable for indices with an
[ident_name] argument to [MakeMonPredAt], but this is not implemented. *)
Global Instance into_exist_monPred_at_ex P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → IntoExist ((<subj> P) i) Φ (to_ident_name idx).
Proof.
  rewrite /IntoExist /MakeMonPredAt monPred_at_subjectively=>H. by setoid_rewrite <- H.
Qed.

Global Instance from_forall_monPred_at {A} P (Φ : A → monPred) name (Ψ : A → PROP) i :
  FromForall P Φ name → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → FromForall (P i) Ψ name.
Proof.
  rewrite /FromForall /MakeMonPredAt=><- H. setoid_rewrite <- H.
  by rewrite monPred_at_forall.
Qed.
Global Instance into_forall_monPred_at {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  IntoForall P Φ → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → IntoForall (P i) Ψ.
Proof.
  rewrite /IntoForall /MakeMonPredAt=>-> H. setoid_rewrite <- H.
  by rewrite monPred_at_forall.
Qed.

(* Framing. *)
Global Instance frame_monPred_at_enter p i 𝓡 P 𝓠 :
  FrameMonPredAt p i 𝓡 P 𝓠 → Frame p 𝓡 (P i) 𝓠 | 2.
Proof. intros. done. Qed.
Global Instance frame_monPred_at_here p P i j :
  IsBiIndexRel i j → FrameMonPredAt p j (P i) P emp | 0.
Proof.
  rewrite /FrameMonPredAt /IsBiIndexRel right_id bi.intuitionistically_if_elim=> -> //.
Qed.

Global Instance frame_monPred_at_embed p 𝓡 𝓠 𝓟 i :
  Frame p 𝓡 𝓟 𝓠 → FrameMonPredAt p i 𝓡 (embed (B:=monPredI) 𝓟) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_embed. Qed.
Global Instance frame_monPred_at_sep p P Q 𝓡 𝓠 i :
  Frame p 𝓡 (P i ∗ Q i) 𝓠 → FrameMonPredAt p i 𝓡 (P ∗ Q) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_sep. Qed.
Global Instance frame_monPred_at_and p P Q 𝓡 𝓠 i :
  Frame p 𝓡 (P i ∧ Q i) 𝓠 → FrameMonPredAt p i 𝓡 (P ∧ Q) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_and. Qed.
Global Instance frame_monPred_at_or p P Q 𝓡 𝓠 i :
  Frame p 𝓡 (P i ∨ Q i) 𝓠 → FrameMonPredAt p i 𝓡 (P ∨ Q) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_or. Qed.
Global Instance frame_monPred_at_wand p P R Q1 Q2 i j :
  IsBiIndexRel i j →
  Frame p R Q1 Q2 →
  FrameMonPredAt p j (R i) (P -∗ Q1) ((P -∗ Q2) i).
Proof.
  rewrite /IsBiIndexRel /Frame /FrameMonPredAt=>-> Hframe.
  rewrite -monPred_at_intuitionistically_if -monPred_at_sep. apply monPred_in_entails.
  change ((□?p R ∗ (P -∗ Q2)) ⊢ P -∗ Q1). apply bi.wand_intro_r.
  rewrite -assoc bi.wand_elim_l. done.
Qed.
Global Instance frame_monPred_at_impl P R Q1 Q2 i j :
  IsBiIndexRel i j →
  Frame true R Q1 Q2 →
  FrameMonPredAt true j (R i) (P → Q1) ((P → Q2) i).
Proof.
  rewrite /IsBiIndexRel /Frame /FrameMonPredAt=>-> Hframe.
  rewrite -monPred_at_intuitionistically_if -monPred_at_sep. apply monPred_in_entails.
  change ((□ R ∗ (P → Q2)) ⊢ P → Q1).
  rewrite -bi.persistently_and_intuitionistically_sep_l. apply bi.impl_intro_r.
  rewrite -assoc bi.impl_elim_l bi.persistently_and_intuitionistically_sep_l. done.
Qed.
Global Instance frame_monPred_at_forall {X : Type} p (Ψ : X → monPred) 𝓡 𝓠 i :
  Frame p 𝓡 (∀ x, Ψ x i) 𝓠 → FrameMonPredAt p i 𝓡 (∀ x, Ψ x) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_forall. Qed.
Global Instance frame_monPred_at_exist {X : Type} p (Ψ : X → monPred) 𝓡 𝓠 i :
  Frame p 𝓡 (∃ x, Ψ x i) 𝓠 → FrameMonPredAt p i 𝓡 (∃ x, Ψ x) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_exist. Qed.

Global Instance frame_monPred_at_absorbingly p P 𝓡 𝓠 i :
  Frame p 𝓡 (<absorb> P i) 𝓠 → FrameMonPredAt p i 𝓡 (<absorb> P) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_absorbingly. Qed.
Global Instance frame_monPred_at_affinely p P 𝓡 𝓠 i :
  Frame p 𝓡 (<affine> P i) 𝓠 → FrameMonPredAt p i 𝓡 (<affine> P) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_affinely. Qed.
Global Instance frame_monPred_at_persistently p P 𝓡 𝓠 i :
  Frame p 𝓡 (<pers> P i) 𝓠 → FrameMonPredAt p i 𝓡 (<pers> P) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_persistently. Qed.
Global Instance frame_monPred_at_intuitionistically p P 𝓡 𝓠 i :
  Frame p 𝓡 (□ P i) 𝓠 → FrameMonPredAt p i 𝓡 (□ P) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_intuitionistically. Qed.
Global Instance frame_monPred_at_objectively p P 𝓡 𝓠 i :
  Frame p 𝓡 (∀ i, P i) 𝓠 → FrameMonPredAt p i 𝓡 (<obj> P) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_objectively. Qed.
Global Instance frame_monPred_at_subjectively p P 𝓡 𝓠 i :
  Frame p 𝓡 (∃ i, P i) 𝓠 → FrameMonPredAt p i 𝓡 (<subj> P) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_subjectively. Qed.
Global Instance frame_monPred_at_bupd `{!BiBUpd PROP} p P 𝓡 𝓠 i :
  Frame p 𝓡 (|==> P i) 𝓠 → FrameMonPredAt p i 𝓡 (|==> P) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_bupd. Qed.

Global Instance into_embed_objective P :
  Objective P → IntoEmbed P (∀ i, P i).
Proof.
  rewrite /IntoEmbed=> ?.
  by rewrite {1}(objective_objectively P) monPred_objectively_unfold.
Qed.

Global Instance elim_modal_at_bupd_goal `{!BiBUpd PROP} φ p p' 𝓟 𝓟' Q Q' i :
  ElimModal φ p p' 𝓟 𝓟' (|==> Q i) (|==> Q' i) →
  ElimModal φ p p' 𝓟 𝓟' ((|==> Q) i) ((|==> Q') i).
Proof. by rewrite /ElimModal !monPred_at_bupd. Qed.
Global Instance elim_modal_at_bupd_hyp `{!BiBUpd PROP} φ p p' P 𝓟 𝓟' 𝓠 𝓠' i:
  MakeMonPredAt i P 𝓟 →
  ElimModal φ p p' (|==> 𝓟) 𝓟' 𝓠 𝓠' →
  ElimModal φ p p' ((|==> P) i) 𝓟' 𝓠 𝓠'.
Proof. by rewrite /MakeMonPredAt /ElimModal monPred_at_bupd=><-. Qed.
Global Instance elim_modal_at φ p p' 𝓟 𝓟' P P' V:
  ElimModal φ p p' ⎡𝓟⎤ ⎡𝓟'⎤ P P' → ElimModal φ p p' 𝓟 𝓟' (P V) (P' V).
Proof.
  rewrite /ElimModal -!embed_intuitionistically_if.
  iIntros (HH Hφ) "[? HP]". iApply HH; [done|]. iFrame. iIntros (? <-) "?".
  by iApply "HP".
Qed.

Global Instance add_modal_at_bupd_goal `{!BiBUpd PROP} φ 𝓟 𝓟' Q i :
  AddModal 𝓟 𝓟' (|==> Q i)%I → AddModal 𝓟 𝓟' ((|==> Q) i).
Proof. by rewrite /AddModal !monPred_at_bupd. Qed.

Global Instance from_forall_monPred_at_plainly `{!Sbi PROP} i P Φ :
  (∀ i, MakeMonPredAt i P (Φ i)) →
  FromForall ((■ P) i) (λ j, ■ (Φ j))%I (to_ident_name idx).
Proof.
  rewrite /FromForall /MakeMonPredAt=>HPΦ. rewrite monPred_at_plainly.
  by setoid_rewrite HPΦ.
Qed.
Global Instance into_forall_monPred_at_plainly `{!Sbi PROP} i P Φ :
  (∀ i, MakeMonPredAt i P (Φ i)) →
  IntoForall ((■ P) i) (λ j, ■ (Φ j))%I.
Proof.
  rewrite /IntoForall /MakeMonPredAt=>HPΦ. rewrite monPred_at_plainly.
  by setoid_rewrite HPΦ.
Qed.

Global Instance is_except_0_monPred_at i P :
  IsExcept0 P → IsExcept0 (P i).
Proof. rewrite /IsExcept0=>- [/(_ i)]. by rewrite monPred_at_except_0. Qed.

Global Instance make_monPred_at_internal_eq `{!Sbi PROP} {A : ofe} (x y : A) i :
  MakeMonPredAt i (x ≡ y) (x ≡ y).
Proof. by rewrite /MakeMonPredAt monPred_at_internal_eq. Qed.
Global Instance make_monPred_at_except_0 i P 𝓠 :
  MakeMonPredAt i P 𝓠 → MakeMonPredAt i (◇ P) (◇ 𝓠).
Proof. by rewrite /MakeMonPredAt monPred_at_except_0=><-. Qed.
Global Instance make_monPred_at_later i P 𝓠 :
  MakeMonPredAt i P 𝓠 → MakeMonPredAt i (▷ P) (▷ 𝓠).
Proof. by rewrite /MakeMonPredAt monPred_at_later=><-. Qed.
Global Instance make_monPred_at_laterN i n P 𝓠 :
  MakeMonPredAt i P 𝓠 → MakeMonPredAt i (▷^n P) (▷^n 𝓠).
Proof. rewrite /MakeMonPredAt=> <-. elim n=>//= ? <-. by rewrite monPred_at_later. Qed.
Global Instance make_monPred_at_fupd `{!BiFUpd PROP} i E1 E2 P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (|={E1,E2}=> P) (|={E1,E2}=> 𝓟).
Proof. by rewrite /MakeMonPredAt monPred_at_fupd=> <-. Qed.

Global Instance into_internal_eq_monPred_at `{!Sbi PROP}
    {A : ofe} (x y : A) P i :
  IntoInternalEq P x y → IntoInternalEq (P i) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite monPred_at_internal_eq. Qed.

Global Instance into_except_0_monPred_at_fwd i P Q 𝓠 :
  IntoExcept0 P Q → MakeMonPredAt i Q 𝓠 → IntoExcept0 (P i) 𝓠.
Proof. rewrite /IntoExcept0 /MakeMonPredAt=> -> <-. by rewrite monPred_at_except_0. Qed.
Global Instance into_except_0_monPred_at_bwd i P 𝓟 Q :
  IntoExcept0 P Q → MakeMonPredAt i P 𝓟 → IntoExcept0 𝓟 (Q i).
Proof. rewrite /IntoExcept0 /MakeMonPredAt=> H <-. by rewrite H monPred_at_except_0. Qed.

Global Instance maybe_into_later_monPred_at i n P Q 𝓠 :
  IntoLaterN false n P Q → MakeMonPredAt i Q 𝓠 →
  IntoLaterN false n (P i) 𝓠.
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN /MakeMonPredAt=> -> <-. elim n=>//= ? <-.
  by rewrite monPred_at_later.
Qed.
Global Instance from_later_monPred_at i φ `(sel : A) n P Q 𝓠 :
  FromModal φ (modality_laterN n) sel P Q →
  MakeMonPredAt i Q 𝓠 →
  FromModal φ (modality_laterN n) sel (P i) 𝓠.
Proof.
  rewrite /FromModal /MakeMonPredAt=> HPQ <- ?. rewrite -HPQ //.
  elim n=>//= ? ->.
  by rewrite monPred_at_later.
Qed.

Global Instance frame_monPred_at_later p P 𝓡 𝓠 i :
  Frame p 𝓡 (▷ P i) 𝓠 → FrameMonPredAt p i 𝓡 (▷ P) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_later. Qed.
Global Instance frame_monPred_at_laterN p n P 𝓡 𝓠 i :
  Frame p 𝓡 (▷^n P i) 𝓠 → FrameMonPredAt p i 𝓡 (▷^n P) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_laterN. Qed.
Global Instance frame_monPred_at_fupd `{!BiFUpd PROP} E1 E2 p P 𝓡 𝓠 i :
  Frame p 𝓡 (|={E1,E2}=> P i) 𝓠 → FrameMonPredAt p i 𝓡 (|={E1,E2}=> P) 𝓠.
Proof. rewrite /Frame /FrameMonPredAt=> ->. by rewrite monPred_at_fupd. Qed.
End bi.
(* When P and/or Q are evars when doing typeclass search on [IntoWand
   (R i) P Q], we use [MakeMonPredAt] in order to normalize the
   result of unification. However, when they are not evars, we want to
   propagate the known information through typeclass search. Hence, we
   do not want to use [MakeMonPredAt].

   As a result, depending on P and Q being evars, we use a different
   version of [into_wand_monPred_at_xx_xx]. *)
Global Hint Extern 3 (IntoWand _ _ (monPred_at _ _) ?P ?Q) =>
     is_evar P; is_evar Q;
     eapply @into_wand_monPred_at_unknown_unknown
     : typeclass_instances.
Global Hint Extern 2 (IntoWand _ _ (monPred_at _ _) ?P (monPred_at ?Q _)) =>
     eapply @into_wand_monPred_at_unknown_known
     : typeclass_instances.
Global Hint Extern 2 (IntoWand _ _ (monPred_at _ _) (monPred_at ?P _) ?Q) =>
     eapply @into_wand_monPred_at_known_unknown_le
     : typeclass_instances.
Global Hint Extern 2 (IntoWand _ _ (monPred_at _ _) (monPred_at ?P _) ?Q) =>
     eapply @into_wand_monPred_at_known_unknown_ge
     : typeclass_instances.

Section modal.
Context {I : biIndex} {PROP : bi}.
Local Notation monPred := (monPred I PROP).
Implicit Types P Q R : monPred.
Implicit Types 𝓟 𝓠 𝓡 : PROP.
Implicit Types φ : Prop.
Implicit Types i j : I.

Global Instance elim_modal_at_fupd_goal `{!BiFUpd PROP} φ p p' E1 E2 E3 𝓟 𝓟' Q Q' i :
  ElimModal φ p p' 𝓟 𝓟' (|={E1,E3}=> Q i) (|={E2,E3}=> Q' i) →
  ElimModal φ p p' 𝓟 𝓟' ((|={E1,E3}=> Q) i) ((|={E2,E3}=> Q') i).
Proof. by rewrite /ElimModal !monPred_at_fupd. Qed.
Global Instance elim_modal_at_fupd_hyp `{!BiFUpd PROP} φ p p' E1 E2 P 𝓟 𝓟' 𝓠 𝓠' i :
  MakeMonPredAt i P 𝓟 →
  ElimModal φ p p' (|={E1,E2}=> 𝓟) 𝓟' 𝓠 𝓠' →
  ElimModal φ p p' ((|={E1,E2}=> P) i) 𝓟' 𝓠 𝓠'.
Proof. by rewrite /MakeMonPredAt /ElimModal monPred_at_fupd=><-. Qed.

Global Instance elim_acc_at_None `{!BiFUpd PROP} {X} φ E1 E2 E3 E4 α α' β β' P P'x i :
  (∀ x, MakeEmbed (α x) (α' x)) → (∀ x, MakeEmbed (β x) (β' x)) →
  ElimAcc (X:=X) φ (fupd E1 E2) (fupd E3 E4) α' β' (λ _, None) P P'x →
  ElimAcc (X:=X) φ (fupd E1 E2) (fupd E3 E4) α β (λ _, None) (P i) (λ x, P'x x i).
Proof.
  rewrite /ElimAcc /MakeEmbed. iIntros (Hα Hβ HEA ?) "Hinner Hacc".
  iApply (HEA with "[Hinner]"); first done.
  - iIntros (x).  iSpecialize ("Hinner" $! x). rewrite -Hα. by iIntros (? <-).
  - iMod "Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". iModIntro. iExists x.
    rewrite -Hα -Hβ. iFrame. iIntros (? _) "Hβ". by iApply "Hclose".
Qed.
Global Instance elim_acc_at_Some `{!BiFUpd PROP} {X} φ E1 E2 E3 E4 α α' β β' γ γ' P P'x i :
  (∀ x, MakeEmbed (α x) (α' x)) →
  (∀ x, MakeEmbed (β x) (β' x)) →
  (∀ x, MakeEmbed (γ x) (γ' x)) →
  ElimAcc (X:=X) φ (fupd E1 E2) (fupd E3 E4) α' β' (λ x, Some (γ' x)) P P'x →
  ElimAcc (X:=X) φ (fupd E1 E2) (fupd E3 E4) α β (λ x, Some (γ x)) (P i) (λ x, P'x x i).
Proof.
  rewrite /ElimAcc /MakeEmbed. iIntros (Hα Hβ Hγ HEA ?) "Hinner Hacc".
  iApply (HEA with "[Hinner]"); first done.
  - iIntros (x).  iSpecialize ("Hinner" $! x). rewrite -Hα. by iIntros (? <-).
  - iMod "Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". iModIntro. iExists x.
    rewrite -Hα -Hβ -Hγ. iFrame. iIntros (? _) "Hβ /=". by iApply "Hclose".
Qed.

Global Instance add_modal_at_fupd_goal `{!BiFUpd PROP} E1 E2 𝓟 𝓟' Q i :
  AddModal 𝓟 𝓟' (|={E1,E2}=> Q i) → AddModal 𝓟 𝓟' ((|={E1,E2}=> Q) i).
Proof. by rewrite /AddModal !monPred_at_fupd. Qed.

(* This hard-codes the fact that ElimInv with_close returns a
   [(λ _, ...)] as Q'. *)
Global Instance elim_inv_embed_with_close {X : Type} φ
    𝓟inv 𝓟in (𝓟out 𝓟close : X → PROP)
    Pin (Pout Pclose : X → monPred)
    Q Q' :
  (∀ i, ElimInv φ 𝓟inv 𝓟in 𝓟out (Some 𝓟close) (Q i) (λ _, Q' i)) →
  MakeEmbed 𝓟in Pin → (∀ x, MakeEmbed (𝓟out x) (Pout x)) →
  (∀ x, MakeEmbed (𝓟close x) (Pclose x)) →
  ElimInv (X:=X) φ ⎡𝓟inv⎤ Pin Pout (Some Pclose) Q (λ _, Q').
Proof.
  rewrite /MakeEmbed /ElimInv=>H <- Hout Hclose ?. iStartProof PROP.
  setoid_rewrite <-Hout. setoid_rewrite <-Hclose.
  iIntros (?) "(?&?&HQ')". iApply H; [done|]. iFrame. iIntros (x) "?".
  by iApply "HQ'".
Qed.
Global Instance elim_inv_embed_without_close  {X : Type}
    φ 𝓟inv 𝓟in (𝓟out : X → PROP) Pin (Pout : X → monPred) Q (Q' : X → monPred) :
  (∀ i, ElimInv φ 𝓟inv 𝓟in 𝓟out None (Q i) (λ x, Q' x i)) →
  MakeEmbed 𝓟in Pin → (∀ x, MakeEmbed (𝓟out x) (Pout x)) →
  ElimInv (X:=X) φ ⎡𝓟inv⎤ Pin Pout None Q Q'.
Proof.
  rewrite /MakeEmbed /ElimInv=>H <-Hout ?. iStartProof PROP.
  setoid_rewrite <-Hout.
  iIntros (?) "(?&?&HQ')". iApply H; [done|]. iFrame. iIntros (x) "?".
  by iApply "HQ'".
Qed.
End modal.
