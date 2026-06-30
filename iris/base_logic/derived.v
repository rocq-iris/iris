From iris.algebra Require Import frac.
From iris.bi Require Export bi.
From iris.base_logic Require Export bi.
Import bi.bi base_logic.bi.uPred.

(** Derived laws for Iris-specific primitive connectives (own, valid).
    This file does NOT unseal! *)

Module uPred.
Section derived.
  Context {M : ucmra}.
  Implicit Types φ : Prop.
  Implicit Types P Q : uPred M.
  Implicit Types A : Type.

  (* Force implicit argument M *)
  Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P Q).
  Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).

  (** Propers *)
  Global Instance ownM_proper: Proper ((≡) ==> (⊣⊢)) (@uPred_ownM M) := ne_proper _.

  (** Own and valid derived *)
  Lemma intuitionistically_ownM (a : M) : CoreId a → □ uPred_ownM a ⊣⊢ uPred_ownM a.
  Proof.
    rewrite /bi_intuitionistically affine_affinely=>?; apply (anti_symm _);
      [by rewrite persistently_elim|].
    by rewrite {1}persistently_ownM_core core_id_core.
  Qed.
  Lemma ownM_invalid (a : M) : ¬ ✓{0} a → uPred_ownM a ⊢ False.
  Proof.
    intros. rewrite ownM_valid internal_cmra_valid_elim. by apply pure_elim'.
  Qed.
  Global Instance ownM_mono : Proper (flip (≼) ==> (⊢)) (@uPred_ownM M).
  Proof. intros a b [b' ->]. by rewrite ownM_op sep_elim_l. Qed.
  Lemma ownM_unit' : uPred_ownM ε ⊣⊢ True.
  Proof. apply (anti_symm _); first by apply pure_intro. apply ownM_unit. Qed.

  Lemma bupd_ownM_update x y : x ~~> y → uPred_ownM x ⊢ |==> uPred_ownM y.
  Proof.
    intros; rewrite (bupd_ownM_updateP _ (y =.)); last by apply cmra_update_updateP.
    by apply bupd_mono, exist_elim=> y'; apply pure_elim_l=> ->.
  Qed.

  (** Timeless instances *)
  Global Instance ownM_timeless (a : M) : Discrete a → Timeless (uPred_ownM a).
  Proof.
    intros ?. rewrite /Timeless later_ownM. apply exist_elim=> b.
    rewrite (timeless (a≡b)) (except_0_intro (uPred_ownM b)) -except_0_and.
    apply except_0_mono. rewrite internal_eq_sym.
    apply (internal_eq_rewrite' b a (uPred_ownM) _);
      [solve_proper|auto using and_elim_l, and_elim_r..].
  Qed.

  (** Persistence *)
  Global Instance ownM_persistent a : CoreId a → Persistent (@uPred_ownM M a).
  Proof.
    intros. rewrite /Persistent -{2}(core_id_core a). apply persistently_ownM_core.
  Qed.

  (** For big ops *)
  Global Instance uPred_ownM_sep_homomorphism :
    MonoidHomomorphism op uPred_sep (≡) (@uPred_ownM M).
  Proof. split; [split|]; try apply _; [apply ownM_op | apply ownM_unit']. Qed.

  (** Soundness statement for our modalities: facts derived under modalities in
  the empty context also without the modalities.
  For basic updates, soundness only holds for plain propositions. *)
  Lemma bupd_soundness P `{!Plain P} : (⊢ |==> P) → ⊢ P.
  Proof. rewrite bupd_elim. done. Qed.

  (** As pure demonstration, we also show that this holds for an arbitrary nesting
  of modalities. We have to do a bit of work to be able to state this theorem
  though. *)
  Inductive modality := MBUpd | MLater | MPersistently | MPlainly.
  Definition denote_modality (m : modality) : uPred M → uPred M :=
    match m with
    | MBUpd => bupd
    | MLater => bi_later
    | MPersistently => bi_persistently
    | MPlainly => plainly
    end.
  Definition denote_modalities (ms : list modality) : uPred M → uPred M :=
    λ P, foldr denote_modality P ms.

  (** Now we can state and prove 'soundness under arbitrary modalities' for plain
  propositions. This is probably not a lemma you want to actually use. *)
  Corollary modal_soundness P `{!Plain P} (ms : list modality) :
    (⊢ denote_modalities ms P) → ⊢ P.
  Proof.
    intros H. apply (laterN_soundness _ (length ms)).
    move: H. apply bi_emp_valid_mono.
    induction ms as [|m ms IH]; first done; simpl.
    destruct m; simpl; rewrite IH.
    - rewrite -later_intro. apply: bupd_elim.
    - done.
    - rewrite -later_intro persistently_elim. done.
    - rewrite -later_intro plainly_elim. done.
  Qed.

  (** Consistency: one cannot deive [False] in the logic, not even under
  modalities. Again this is just for demonstration and probably not practically
  useful. *)
  Corollary consistency : ¬ ⊢@{uPredI M} False.
  Proof. apply: pure_soundness. Qed.
End derived.
End uPred.
