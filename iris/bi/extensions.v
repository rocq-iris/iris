(** This file defines various extensions to the base BI interface, via
typeclasses that BIs can optionally implement. *)

From iris.bi Require Export derived_connectives.

Class BiAffine {SI : sidx} (PROP : bi) := absorbing_bi (Q : PROP) : Affine Q.
Global Hint Mode BiAffine - ! : typeclass_instances.
Global Existing Instance absorbing_bi | 0.

Class BiPositive {SI : sidx} (PROP : bi) :=
  bi_positive (P Q : PROP) : <affine> (P ∗ Q) ⊢ <affine> P ∗ Q.
Global Hint Mode BiPositive - ! : typeclass_instances.

(** The class [BiLöb] is required for the [iLöb] tactic. However, for most BI
logics the class [Sbi] should be used, which gives an instance of [BiLöb]
automatically (see [derived_laws_later]). A direct instance of [BiLöb] is useful
when considering a BI logic with a discrete OFE, instead of an OFE that takes
step-indexing of the logic in account.

The internal/"strong" version of Löb [(▷ P → P) ⊢ P] is derivable from [BiLöb].
It is provided by the lemma [löb] in [derived_laws_later]. *)
Class BiLöb {SI : sidx} (PROP : bi) :=
  löb_weak (P : PROP) : (▷ P ⊢ P) → (True ⊢ P).
Global Hint Mode BiLöb - ! : typeclass_instances.
Global Arguments löb_weak {SI _ _} _ _.

(** One should not instantiate this class, and instead provide an instance of
[Sbi], from which one gets an instance of [BiLaterContractive] for free. *)
Class BiLaterContractive {SI : sidx} (PROP : bi) :=
  #[global] later_contractive :: Contractive (bi_later (PROP:=PROP)).

(** The class [BiPersistentlyForall] states that universal quantification
commutes with the persistently modality. The reverse direction of the entailment
described by this type class is derivable, so it is not included.

Main consequences of inhabiting this class:
- We have [Persistent (∀ x, Ψ x)] provided [∀ x, Persistent (Ψ x)]. *)
Class BiPersistentlyForall {SI : sidx} (PROP : bi) :=
  persistently_forall_2 : ∀ {A} (Ψ : A → PROP), (∀ a, <pers> (Ψ a)) ⊢ <pers> (∀ a, Ψ a).
Global Hint Mode BiPersistentlyForall - ! : typeclass_instances.

(** The class [BiPersistentlyExist] states that existential quantification
commutes with the persistently modality. The reverse direction of the entailment
described by this type class is derivable, so it is not included.

Main consequences of inhabiting this class:
- When performing [iDestruct] on a hypothesis [H : P ∨ Q] or [H : ∃ x, P] in the
  persistent context, the result remains there. If the class is not inhabited,
  the resulting hypothesis is moved to the spatial context.
- The persistence modality preserves [Timeless]. *)
Class BiPersistentlyExist {SI : sidx} (PROP : bi) :=
  persistently_exist_1 : ∀ {A} (Ψ : A → PROP),
    <pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> Ψ a.
Global Hint Mode BiPersistentlyExist - ! : typeclass_instances.

(** The class [BiPureForall] states that universal quantification commutes with
the embedding of pure propositions. The reverse direction of the entailment
described by this type class is derivable, so it is not included.

An instance of [BiPureForall] itself is derivable if we assume excluded middle
in Rocq, see the lemma [bi_pure_forall_em] in [derived_laws]. *)
Class BiPureForall {SI : sidx} (PROP : bi) :=
  pure_forall_2 : ∀ {A} (φ : A → Prop), (∀ a, ⌜ φ a ⌝) ⊢@{PROP} ⌜ ∀ a, φ a ⌝.
Global Hint Mode BiPureForall - ! : typeclass_instances.
