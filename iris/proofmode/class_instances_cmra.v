From iris.proofmode Require Import modality_instances classes.
Import bi.

Section class_instances_cmra_valid.
  Context `{!Sbi PROP}.

  Global Instance into_pure_internal_cmra_valid `{!CmraDiscrete A} (a : A) :
    @IntoPure PROP (✓ a) (✓ a).
  Proof. by rewrite /IntoPure internal_cmra_valid_discrete. Qed.

  Global Instance from_pure_internal_cmra_valid {A : cmra} (a : A) :
    @FromPure PROP false (✓ a) (✓ a).
  Proof.
    rewrite /FromPure /=. apply bi.pure_elim'=> ?.
    rewrite -internal_cmra_valid_intro //.
  Qed.

  Global Instance into_pure_internal_included {A : cmra} (a b : A) `{!Discrete b} :
    @IntoPure PROP (a ≼ b) (a ≼ b).
  Proof. by rewrite /IntoPure internal_included_discrete. Qed.

  Global Instance from_pure_internal_included {A : cmra} (a b : A) :
    @FromPure PROP false (a ≼ b) (a ≼ b).
  Proof.
    rewrite /FromPure /=. apply bi.pure_elim'=> ?.
    rewrite -internal_included_intro //.
  Qed.

  Global Instance into_exist_internal_included {A : cmra} (a b : A) :
    IntoExist (PROP:=PROP) (a ≼ b) (λ c, b ≡ a ⋅ c)%I (λ x, x).
  Proof. by rewrite /IntoExist. Qed.

  Global Instance from_exist_internal_included {A : cmra} (a b : A) :
    FromExist (PROP:=PROP) (a ≼ b) (λ c, b ≡ a ⋅ c)%I.
  Proof. by rewrite /FromExist. Qed.
End class_instances_cmra_valid.
