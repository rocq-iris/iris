From iris.algebra Require Import ofe.
From iris.prelude Require Import options.

(** The definition of [chain] can be found in [ofe.v], and is used to define
    COFEs. In this file, we show that [chain] is also a closure operation on OFEs.

    When using finite step-indexing, we define the closure of an OFE [A]
    as [chain A]. The completion of [chain (chain A)] is given by the diagonal,
    and, if [A] is a COFE, the isomorphism [A ≃ chain A] is given by:
    - [chain_const : A → chain A]
    - [compl : chain A → A] *)
Section ofe.
  Context {SI : sidx} {A : ofe}.

  Local Instance chain_dist : Dist (chain A) := λ n c1 c2,
    ∀ m, (m ≤ n)%sidx → c1 m ≡{m}≡ c2 m.
  Local Instance chain_equiv : Equiv (chain A) := λ c1 c2,
    ∀ n, c1 n ≡{n}≡ c2 n.

  Lemma chain_ofe_mixin : OfeMixin (chain A).
  Proof.
    split; rewrite /dist /equiv.
    - intros c1 c2. split.
      + intros H n m ?. apply H.
      + intros H n. by apply (H n).
    - intros n. split.
      + by intros c m ?.
      + intros c1 c2 H m ?. symmetry. by apply H.
      + intros c1 c2 c3 H H' m ?. trans (c2 m); auto.
    - intros n m c1 c2 H ? k ?. apply H. by etrans.
  Qed.
  Canonical Structure chainO : ofe := Ofe (chain A) chain_ofe_mixin.

  Program Definition chain_compl : Compl chainO := λ cc,
    {| chain_car n := cc n n |}.
  Next Obligation.
    intros cc n m ?. simpl.
    rewrite (chain_cauchy (cc m) n m) //.
    by apply (chain_cauchy cc n m).
  Qed.

  Global Program Instance chain_cofe `{!SIdxFinite SI} : Cofe chainO :=
    cofe_finite chain_compl _.
  Next Obligation.
    intros ? n cc m Hle. simpl.
    by rewrite (chain_cauchy cc m n Hle m).
  Qed.

  Global Instance chain_const_ne : NonExpansive chain_const.
  Proof. intros n ??? m ?. by eapply dist_le'. Qed.
  Global Instance chain_const_proper : Proper ((≡) ==> (≡)) chain_const.
  Proof. apply: ne_proper. Qed.
  Global Instance compl_ne `{!Cofe A} : NonExpansive (compl (A:=A)).
  Proof. intros n c1 c2 H. rewrite !conv_compl. by apply H. Qed.
  Global Instance compl_proper `{!Cofe A} : Proper ((≡) ==> (≡)) (compl (A:=A)).
  Proof. apply: ne_proper. Qed.

  Program Definition chain_iso `{!Cofe A} : ofe_iso A chainO := {|
    ofe_iso_1 := OfeMor chain_const;
    ofe_iso_2 := OfeMor compl;
  |}.
  Next Obligation. intros ? c n. apply conv_compl. Qed.
  Next Obligation. intros ? a. apply equiv_dist=> n. apply conv_compl. Qed.
End ofe.

Global Arguments chainO {_} _ : assert.

Global Instance chain_inhabited {SI : sidx} {A : ofe} `{!Inhabited A} :
    Inhabited (chain A) :=
  populate (chain_const inhabitant).

Section chain_map.
  Context {SI : sidx}.

  Global Instance chain_map_ne {A B : ofe} (f : A → B) `{!NonExpansive f} :
    NonExpansive (chain_map f).
  Proof. intros n c1 c2 H m ?. simpl. f_equiv. by apply H. Qed.

  Lemma chain_map_id {A : ofe} (c : chain A) :
    chain_map cid c ≡ c.
  Proof. by intros n. Qed.

  Lemma chain_map_compose {A1 A2 A3 : ofe}
      (f : A2 -n> A1) (f' : A3 -n> A2) (c : chain A3) :
    chain_map (f ◎ f') c ≡ chain_map f (chain_map f' c).
  Proof. by intros n. Qed.

  Lemma chain_map_ext_ne {A B : ofe} (f g : A → B) (c : chain A) n
      `{!NonExpansive f, !NonExpansive g} :
    (∀ x, f x ≡{n}≡ g x) → chain_map f c ≡{n}≡ chain_map g c.
  Proof. intros H m ?. apply (dist_le n m); last done. apply H. Qed.
  Lemma chain_map_ext {A B : ofe} (f g : A → B) (c : chain A)
      `{!NonExpansive f, !NonExpansive g} :
    (∀ x, f x ≡ g x) → chain_map f c ≡ chain_map g c.
  Proof.
    intros H. apply equiv_dist=> n.
    apply chain_map_ext_ne=> x. by apply equiv_dist.
  Qed.

  Definition chainO_map {A B : ofe} (f : A -n> B) : chainO A -n> chainO B :=
    OfeMor (chain_map f).
  Global Instance chainO_map_ne (A B: ofe) :
    NonExpansive (@chainO_map A B).
  Proof. intros n f f' Hf c m ?. by eapply dist_le'; last apply Hf. Qed.

  Program Definition chainOF (F : oFunctor) : oFunctor := {|
    oFunctor_car A _ B _ := chainO (oFunctor_car F A B);
    oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := chainO_map (oFunctor_map F fg);
  |}.
  Next Obligation. intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg. by rewrite Hfg. Qed.
  Next Obligation. intros F A ? B ? c m. by rewrite /= oFunctor_map_id. Qed.
  Next Obligation.
    intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' c.
    rewrite /= -chain_map_compose.
    apply chain_map_ext, oFunctor_map_compose.
  Qed.

  Global Instance chainOF_contractive F :
    oFunctorContractive F → oFunctorContractive (chainOF F).
  Proof.
    by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
      apply chainO_map_ne, oFunctor_map_contractive.
  Qed.
End chain_map.
