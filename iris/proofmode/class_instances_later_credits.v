From iris.proofmode Require Import classes.
Import bi.

Section class_instances_later_credits.
  Context {SI : sidx} `{!BiLaterCredits PROP}.
  Implicit Types P Q R : PROP.

  (** Make sure that the rule for [+] is used before [S], otherwise Rocq's
  unification applies the [S] hint too eagerly. See Iris issue #470. *)
  Global Instance from_sep_lc_add n m : FromSep (PROP:=PROP) (£ (n + m)) (£ n) (£ m) | 0.
  Proof. by rewrite /FromSep lc_split. Qed.
  Global Instance from_sep_lc_S n : FromSep (PROP:=PROP) (£ (S n)) (£ 1) (£ n) | 1.
  Proof. by rewrite /FromSep (lc_succ n). Qed.

  (** When combining later credits with [iCombine], the priorities are
  reversed when compared to [FromSep] and [IntoSep]. This causes
  [£ n] and [£ 1] to be combined as [£ (S n)], not as [£ (n + 1)]. *)
  Global Instance combine_sep_lc_add n m :
    CombineSepAs (PROP:=PROP) (£ n) (£ m) (£ (n + m)) | 1.
  Proof. by rewrite /CombineSepAs lc_split. Qed.
  Global Instance combine_sep_lc_S_l n :
    CombineSepAs (PROP:=PROP) (£ n) (£ 1) (£ (S n)) | 0.
  Proof. by rewrite /CombineSepAs comm (lc_succ n). Qed.

  Global Instance into_sep_lc_add n m : IntoSep (PROP:=PROP) (£ (n + m)) (£ n) (£ m) | 0.
  Proof. by rewrite /IntoSep lc_split. Qed.
  Global Instance into_sep_lc_S n : IntoSep (PROP:=PROP) (£ (S n)) (£ 1) (£ n) | 1.
  Proof. by rewrite /IntoSep (lc_succ n). Qed.
End class_instances_later_credits.
