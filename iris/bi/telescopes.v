From stdpp Require Export telescopes.
From iris.bi Require Export bi.
Import bi.

(* This cannot import the proofmode because it is imported by the proofmode! *)

(** Telescopic quantifiers *)
Definition bi_texist {SI : sidx} {PROP : bi} {TT : tele@{Quant}}
    (Ψ : TT → PROP) : PROP :=
  tele_fold (@bi_exist _ PROP) (tele_bind Ψ).
Global Arguments bi_texist {SI _ !_} _ /.
Definition bi_tforall {SI : sidx} {PROP : bi} {TT : tele@{Quant}}
    (Ψ : TT → PROP) : PROP :=
  tele_fold (@bi_forall _ PROP) (tele_bind Ψ).
Global Arguments bi_tforall {SI _ !_} _ /.

Notation "'∃..' x .. y , P" := (bi_texist (λ x, .. (bi_texist (λ y, P)) .. )%I)
  (at level 200, x binder, y binder, right associativity,
  format "∃..  x  ..  y ,  P") : bi_scope.
Notation "'∀..' x .. y , P" := (bi_tforall (λ x, .. (bi_tforall (λ y, P)) .. )%I)
  (at level 200, x binder, y binder, right associativity,
  format "∀..  x  ..  y ,  P") : bi_scope.

Section telescopes.
  Context {SI : sidx} {PROP : bi} {TT : tele@{Quant}}.
  Implicit Types Ψ : TT → PROP.

  Lemma bi_tforall_forall Ψ : bi_tforall Ψ ⊣⊢ bi_forall Ψ.
  Proof.
    unfold bi_tforall. apply (anti_symm _).
    - apply forall_intro. induction TT as [|X ft IH].
      { by intros []. }
      intros [x xs]; simpl. by rewrite (forall_elim x) IH.
    - induction TT as [|X ft IH]; simpl.
      { by rewrite (forall_elim TargO). }
      apply forall_intro=> x. rewrite -IH. apply forall_intro=> xs.
      by rewrite (forall_elim (TargS x xs)).
  Qed.

  Lemma bi_texist_exist Ψ : bi_texist Ψ ⊣⊢ bi_exist Ψ.
  Proof.
    unfold bi_texist. apply (anti_symm _).
    - induction TT as [|X ft IH]; simpl.
      { by rewrite -(exist_intro TargO). }
      apply exist_elim=> x. rewrite IH. apply exist_elim=> xs.
      by rewrite (exist_intro (TargS x xs)).
    - apply exist_elim. induction TT as [|X ft IH].
      { by intros []. }
      intros [x xs]; simpl. by rewrite -(exist_intro x) -IH.
  Qed.

  Global Instance bi_tforall_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_tforall _ PROP TT).
  Proof. intros ?? EQ. rewrite !bi_tforall_forall. rewrite EQ //. Qed.
  Global Instance bi_tforall_proper :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@bi_tforall _ PROP TT).
  Proof. intros ?? EQ. rewrite !bi_tforall_forall. rewrite EQ //. Qed.

  Global Instance bi_texist_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_texist _ PROP TT).
  Proof. intros ?? EQ. rewrite !bi_texist_exist. rewrite EQ //. Qed.
  Global Instance bi_texist_proper :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@bi_texist _ PROP TT).
  Proof. intros ?? EQ. rewrite !bi_texist_exist. rewrite EQ //. Qed.

  Global Instance bi_tforall_absorbing Ψ :
    (∀ x, Absorbing (Ψ x)) → Absorbing (∀.. x, Ψ x).
  Proof. rewrite bi_tforall_forall. apply _. Qed.
  Global Instance bi_tforall_persistent `{!BiPersistentlyForall PROP} Ψ :
    (∀ x, Persistent (Ψ x)) → Persistent (∀.. x, Ψ x).
  Proof. rewrite bi_tforall_forall. apply _. Qed.

  Global Instance bi_texist_affine Ψ :
    (∀ x, Affine (Ψ x)) → Affine (∃.. x, Ψ x).
  Proof. rewrite bi_texist_exist. apply _. Qed.
  Global Instance bi_texist_absorbing Ψ :
    (∀ x, Absorbing (Ψ x)) → Absorbing (∃.. x, Ψ x).
  Proof. rewrite bi_texist_exist. apply _. Qed.
  Global Instance bi_texist_persistent Ψ :
    (∀ x, Persistent (Ψ x)) → Persistent (∃.. x, Ψ x).
  Proof. rewrite bi_texist_exist. apply _. Qed.

  Global Instance bi_tforall_timeless Ψ :
    (∀ x, Timeless (Ψ x)) → Timeless (∀.. x, Ψ x).
  Proof. rewrite bi_tforall_forall. apply _. Qed.

  Global Instance bi_texist_timeless Ψ :
    (∀ x, Timeless (Ψ x)) → Timeless (∃.. x, Ψ x).
  Proof. rewrite bi_texist_exist. apply _. Qed.
End telescopes.
