From iris.algebra Require Import cmra view auth agree csum list excl gmap.
From iris.algebra.lib Require Import excl_auth gmap_view dfrac_agree.
From iris.bi Require Export sbi_unfold derived_laws.
Local Set Default Proof Using "Type*".

Section algebra.
  Context `{!Sbi PROP}.

  (* Force implicit argument [PROP] *)
  Notation "P ⊢ Q" := (bi_entails (PROP:=PROP) P Q).
  Notation "P ⊣⊢ Q" := (equiv (A:=PROP) P%I Q%I).
  Notation "⊢ Q" := (bi_emp_valid (PROP:=PROP) Q).

  Lemma ucmra_unit_validI {A : ucmra} : ⊢ ✓ (ε : A).
  Proof. sbi_unfold. apply ucmra_unit_validN. Qed.
  Lemma cmra_validI_op_r {A : cmra} (x y : A) : ✓ (x ⋅ y) ⊢ ✓ y.
  Proof. sbi_unfold=> n. apply cmra_validN_op_r. Qed.
  Lemma cmra_validI_op_l {A : cmra} (x y : A) : ✓ (x ⋅ y) ⊢ ✓ x.
  Proof. sbi_unfold=> n. apply cmra_validN_op_l. Qed.
  Lemma cmra_later_opI `{!CmraTotal A} (x y1 y2 : A) :
    ▷ (✓ x ∧ x ≡ y1 ⋅ y2) ⊢ ∃ z1 z2, x ≡ z1 ⋅ z2 ∧ ▷ (z1 ≡ y1) ∧ ▷ (z2 ≡ y2).
  Proof.
    sbi_unfold=> -[|n].
    - intros _. exists x, (core x). by rewrite cmra_core_r.
    - intros [??].
      destruct (cmra_extend n x y1 y2) as (z1 & z2 & ? & ? & ?); [done..|].
      exists z1, z2. auto using equiv_dist.
  Qed.
  Lemma cmra_morphism_validI {A B : cmra} (f : A → B) `{!CmraMorphism f} x :
    ✓ x ⊢ ✓ (f x).
  Proof. sbi_unfold=> n. by apply cmra_morphism_validN. Qed.

  Lemma prod_validI {A B : cmra} (x : A * B) : ✓ x ⊣⊢ ✓ x.1 ∧ ✓ x.2.
  Proof. by sbi_unfold. Qed.
  Lemma prod_includedI {A B : cmra} (x y : A * B) :
    x ≼ y ⊣⊢ x.1 ≼ y.1 ∧ x.2 ≼ y.2.
  Proof. sbi_unfold=> n. apply prod_includedN. Qed.

  Lemma option_validI {A : cmra} (mx : option A) :
    ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True end.
  Proof. sbi_unfold=> n. by destruct mx. Qed.
  Lemma option_includedI {A : cmra} (mx my : option A) :
    mx ≼ my ⊣⊢ match mx, my with
               | Some x, Some y => (x ≼ y) ∨ (x ≡ y)
               | None, _ => True
               | Some x, None => False
               end.
  Proof.
    sbi_unfold=> n. destruct mx, my; rewrite ?option_includedN; naive_solver.
  Qed.
  Lemma option_included_totalI `{!CmraTotal A} (mx my : option A) :
    mx ≼ my ⊣⊢ match mx, my with
               | Some x, Some y => x ≼ y
               | None, _ => True
               | Some x, None => False
               end.
  Proof.
    sbi_unfold=> n; destruct mx, my;
      rewrite ?Some_includedN_total ?option_includedN; naive_solver.
  Qed.
  Lemma Some_included_totalI `{!CmraTotal A} (x y : A) :
    Some x ≼ Some y ⊣⊢ x ≼ y.
  Proof. by rewrite option_included_totalI. Qed.

  Lemma discrete_fun_validI {A} {B : A → ucmra} (g : discrete_fun B) :
    ✓ g ⊣⊢ ∀ i, ✓ g i.
  Proof. by sbi_unfold. Qed.

  Lemma f_homom_includedI {A B : cmra} (x y : A) (f : A → B) `{!NonExpansive f} :
    (* This is a slightly weaker condition than being a [CmraMorphism] *)
    (∀ c, f x ⋅ f c ≡ f (x ⋅ c)) →
    (x ≼ y ⊢ f x ≼ f y).
  Proof. intros Hf. sbi_unfold=> n. intros [z ->]. rewrite -Hf. by eexists. Qed.

  (* Analogues of [id_freeN_l] and [id_freeN_r] in the logic, stated in a way
    that allows us to do [iDestruct (id_freeI_r with "H✓ H≡") as %[]]*)
  Lemma id_freeI_r {A : cmra} (x y : A) :
    IdFree x → ⊢@{PROP} ✓ x -∗ (x ⋅ y) ≡ x -∗ False.
  Proof. intros. sbi_unfold. eauto using id_freeN_r. Qed.
  Lemma id_freeI_l {A : cmra} (x y : A) :
    IdFree x → ⊢ ✓ x -∗ (y ⋅ x) ≡ x -∗ False.
  Proof. intros. sbi_unfold. eauto using id_freeN_l. Qed.

  Section gmap_ofe.
    Context `{Countable K} {A : ofe}.
    Implicit Types m : gmap K A.
    Implicit Types i : K.

    Lemma gmap_equivI m1 m2 : m1 ≡ m2 ⊣⊢ ∀ i, m1 !! i ≡ m2 !! i.
    Proof. by sbi_unfold. Qed.

    Lemma gmap_union_equiv_eqI m m1 m2 :
      m ≡ m1 ∪ m2 ⊣⊢ ∃ m1' m2', ⌜ m = m1' ∪ m2' ⌝ ∧ m1' ≡ m1 ∧ m2' ≡ m2.
    Proof. sbi_unfold=> n. apply gmap_union_dist_eq. Qed.
  End gmap_ofe.

  Section gmap_cmra.
    Context `{Countable K} {A : cmra}.
    Implicit Types m : gmap K A.

    Lemma gmap_validI m : ✓ m ⊣⊢ ∀ i, ✓ (m !! i).
    Proof. by sbi_unfold. Qed.
    Lemma singleton_validI i x : ✓ ({[ i := x ]} : gmap K A) ⊣⊢ ✓ x.
    Proof. sbi_unfold=> n. apply singleton_validN. Qed.
  End gmap_cmra.

  Section list_ofe.
    Context {A : ofe}.
    Implicit Types l : list A.

    Lemma list_equivI l1 l2 : l1 ≡ l2 ⊣⊢ ∀ i, l1 !! i ≡ l2 !! i.
    Proof. sbi_unfold. intros n. apply list_dist_lookup. Qed.
  End list_ofe.

  Section excl.
    Context {A : ofe}.
    Implicit Types x : excl A.

    Lemma excl_equivI x y :
      x ≡ y ⊣⊢ match x, y with
                          | Excl a, Excl b => a ≡ b
                          | ExclInvalid, ExclInvalid => True
                          | _, _ => False
                          end.
    Proof.
      sbi_unfold; split; [by destruct 1|destruct x, y; by repeat constructor].
    Qed.

    Lemma excl_validI x :
      ✓ x ⊣⊢ if x is ExclInvalid then False else True.
    Proof. by sbi_unfold. Qed.

    Lemma excl_includedI (x y : excl A) :
      x ≼ y ⊣⊢ ⌜ y = ExclInvalid ⌝.
    Proof. sbi_unfold=> n; apply excl_includedN. Qed.
  End excl.

  Section agree.
    Context {A : ofe}.
    Implicit Types a b : A.
    Implicit Types x y : agree A.

    Lemma agree_equivI a b : to_agree a ≡ to_agree b ⊣⊢ (a ≡ b).
    Proof. sbi_unfold=> n. apply: inj_iff. Qed.
    Lemma agree_op_invI x y : ✓ (x ⋅ y) ⊢ x ≡ y.
    Proof. sbi_unfold=> n. apply agree_op_invN. Qed.

    Lemma to_agree_validI a : ⊢ ✓ to_agree a.
    Proof. by sbi_unfold. Qed.
    Lemma to_agree_op_validI a b : ✓ (to_agree a ⋅ to_agree b) ⊣⊢ a ≡ b.
    Proof. sbi_unfold. apply to_agree_op_validN. Qed.

    Lemma to_agree_uninjI x : ✓ x ⊢ ∃ a, to_agree a ≡ x.
    Proof. sbi_unfold=> n. exact: to_agree_uninjN. Qed.

    (** Derived lemma: If two [x y : agree O] compose to some [to_agree a],
      they are internally equal, and also equal to the [to_agree a].

      Empirically, [x ⋅ y ≡ to_agree a] appears often when agreement comes up
      in CMRA validity terms, especially when [view]s are involved. The desired
      simplification [x ≡ y ∧ y ≡ to_agree a] is also not straightforward to
      derive, so we have a special lemma to handle this common case. *)
    Lemma agree_op_equiv_to_agreeI x y a :
      x ⋅ y ≡ to_agree a ⊢ x ≡ y ∧ y ≡ to_agree a.
    Proof.
      assert (x ⋅ y ≡ to_agree a ⊢ x ≡ y) as Hxy_equiv.
      { rewrite -(agree_op_invI x y) internal_eq_sym.
        apply: (internal_eq_rewrite' _ _ (λ o, ✓ o)%I); [solve_proper|done|].
        rewrite -(bi.absorbing_absorbingly (✓ _)).
        rewrite -to_agree_validI bi.absorbingly_emp_True. apply bi.True_intro. }
      apply bi.and_intro; first done.
      rewrite -{1}(idemp bi_and (_ ≡ _)%I) {1}Hxy_equiv. apply bi.impl_elim_l'.
      apply: (internal_eq_rewrite' _ _
        (λ y', x ⋅ y' ≡ to_agree a → y' ≡ to_agree a)%I); [solve_proper|done|].
      rewrite agree_idemp. apply bi.impl_refl.
    Qed.

    Lemma agree_includedI (x y : agree A) : x ≼ y ⊣⊢ y ≡ x ⋅ y.
    Proof. sbi_unfold=> n. apply agree_includedN. Qed.

    Lemma to_agree_includedI a b : to_agree a ≼ to_agree b ⊣⊢ a ≡ b.
    Proof. sbi_unfold=> n. apply: to_agree_includedN. Qed.
  End agree.

  Section csum_ofe.
    Context {A B : ofe}.
    Implicit Types a : A.
    Implicit Types b : B.

    Lemma csum_equivI (x y : csum A B) :
      x ≡ y ⊣⊢ match x, y with
                          | Cinl a, Cinl a' => a ≡ a'
                          | Cinr b, Cinr b' => b ≡ b'
                          | CsumInvalid, CsumInvalid => True
                          | _, _ => False
                          end.
    Proof.
      sbi_unfold; split; [by destruct 1|destruct x, y; by repeat constructor].
    Qed.
  End csum_ofe.

  Section csum_cmra.
    Context {A B : cmra}.
    Implicit Types a : A.
    Implicit Types b : B.

    Lemma csum_validI (x : csum A B) :
      ✓ x ⊣⊢ match x with
                        | Cinl a => ✓ a
                        | Cinr b => ✓ b
                        | CsumInvalid => False
                        end.
    Proof. by sbi_unfold. Qed.

    Lemma csum_includedI (sx sy : csum A B) :
      sx ≼ sy ⊣⊢ match sx, sy with
                 | Cinl x, Cinl y => x ≼ y
                 | Cinr x, Cinr y => x ≼ y
                 | _, CsumInvalid => True
                 | _, _ => False
                 end.
    Proof.
      sbi_unfold=> n; destruct sx, sy; rewrite ?csum_includedN; naive_solver.
    Qed.
  End csum_cmra.

  Section view.
    Context {A B} (rel : view_rel A B).
    Implicit Types a : A.
    Implicit Types ag : option (frac * agree A).
    Implicit Types b : B.
    Implicit Types x y : view rel.

    Lemma view_both_dfrac_validI_1 (relI : siProp) dq a b :
      (∀ n, rel n a b → siProp_holds relI n) →
      ✓ (●V{dq} a ⋅ ◯V b : view rel) ⊢ ⌜✓dq⌝ ∧ <si_pure> relI.
    Proof.
      intros. sbi_unfold=> n. rewrite view_both_dfrac_validN. naive_solver.
    Qed.
    Lemma view_both_dfrac_validI_2 (relI : siProp) dq a b :
      (∀ n, siProp_holds relI n → rel n a b) →
      ⌜✓dq⌝ ∧ <si_pure> relI ⊢ ✓ (●V{dq} a ⋅ ◯V b : view rel).
    Proof.
      intros. sbi_unfold=> n. rewrite view_both_dfrac_validN. naive_solver.
    Qed.
    Lemma view_both_dfrac_validI (relI : siProp) dq a b :
      (∀ n, rel n a b ↔ siProp_holds relI n) →
      ✓ (●V{dq} a ⋅ ◯V b : view rel) ⊣⊢ ⌜✓dq⌝ ∧ <si_pure> relI.
    Proof.
      intros. apply (anti_symm _);
        [apply view_both_dfrac_validI_1|apply view_both_dfrac_validI_2]; naive_solver.
    Qed.

    Lemma view_both_validI_1 (relI : siProp) a b :
      (∀ n, rel n a b → siProp_holds relI n) →
      ✓ (●V a ⋅ ◯V b : view rel) ⊢ <si_pure> relI.
    Proof. intros. by rewrite view_both_dfrac_validI_1 // bi.and_elim_r. Qed.
    Lemma view_both_validI_2 (relI : siProp) a b :
      (∀ n, siProp_holds relI n → rel n a b) →
      <si_pure> relI ⊢ ✓ (●V a ⋅ ◯V b : view rel).
    Proof.
      intros. rewrite -view_both_dfrac_validI_2 //.
      apply bi.and_intro; [|done]. by apply bi.pure_intro.
    Qed.
    Lemma view_both_validI (relI : siProp) a b :
      (∀ n, rel n a b ↔ siProp_holds relI n) →
      ✓ (●V a ⋅ ◯V b : view rel) ⊣⊢ <si_pure> relI.
    Proof.
      intros. apply (anti_symm _);
        [apply view_both_validI_1|apply view_both_validI_2]; naive_solver.
    Qed.

    Lemma view_auth_dfrac_validI (relI : siProp) dq a :
      (∀ n, siProp_holds relI n ↔ rel n a ε) →
      ✓ (●V{dq} a : view rel) ⊣⊢ ⌜✓dq⌝ ∧ <si_pure> relI.
    Proof.
      intros. rewrite -(right_id ε op (●V{dq} a)). by apply view_both_dfrac_validI.
    Qed.
    Lemma view_auth_validI (relI : siProp) a :
      (∀ n, siProp_holds relI n ↔ rel n a ε) →
      ✓ (●V a : view rel) ⊣⊢ <si_pure> relI.
    Proof. intros. rewrite -(right_id ε op (●V a)). by apply view_both_validI. Qed.

    Lemma view_frag_validI (relI : siProp) b :
      (∀ n, siProp_holds relI n ↔ ∃ a, rel n a b) →
      ✓ (◯V b : view rel) ⊣⊢ <si_pure> relI.
    Proof. intros Hrel. sbi_unfold=> n. by rewrite Hrel. Qed.
  End view.

  Section auth.
    Context {A : ucmra}.
    Implicit Types a b : A.
    Implicit Types x y : auth A.

    Lemma auth_auth_dfrac_validI dq a : ✓ (●{dq} a) ⊣⊢ ⌜✓dq⌝ ∧ ✓ a.
    Proof. sbi_unfold=> n. apply auth_auth_dfrac_validN. Qed.
    Lemma auth_auth_validI a : ✓ (● a) ⊣⊢ ✓ a.
    Proof. sbi_unfold=> n. apply auth_auth_validN. Qed.
    Lemma auth_auth_dfrac_op_validI dq1 dq2 a1 a2 :
      ✓ (●{dq1} a1 ⋅ ●{dq2} a2) ⊣⊢ ✓ (dq1 ⋅ dq2) ∧ (a1 ≡ a2) ∧ ✓ a1.
    Proof. sbi_unfold=> n. apply auth_auth_dfrac_op_validN. Qed.

    Lemma auth_frag_validI a : ✓ (◯ a) ⊣⊢ ✓ a.
    Proof. sbi_unfold=> n. apply auth_frag_validN. Qed.

    Lemma auth_both_dfrac_validI dq a b :
      ✓ (●{dq} a ⋅ ◯ b) ⊣⊢ ⌜✓dq⌝ ∧ (∃ c, a ≡ b ⋅ c) ∧ ✓ a.
    Proof.  sbi_unfold=> n. apply auth_both_dfrac_validN. Qed.
    Lemma auth_both_validI a b :
      ✓ (● a ⋅ ◯ b) ⊣⊢ (∃ c, a ≡ b ⋅ c) ∧ ✓ a.
    Proof. sbi_unfold=> n. apply auth_both_validN. Qed.
  End auth.

  Section excl_auth.
    Context {A : ofe}.
    Implicit Types a b : A.

    Lemma excl_auth_agreeI a b : ✓ (●E a ⋅ ◯E b) ⊢ (a ≡ b).
    Proof. sbi_unfold=> n. apply excl_auth_agreeN. Qed.
  End excl_auth.

  Section dfrac_agree.
    Context {A : ofe}.
    Implicit Types a b : A.

    Lemma dfrac_agree_validI dq a : ✓ (to_dfrac_agree dq a) ⊣⊢ ⌜✓ dq⌝.
    Proof. sbi_unfold=> n. rewrite /to_dfrac_agree pair_validN. naive_solver. Qed.

    Lemma dfrac_agree_validI_2 dq1 dq2 a b :
      ✓ (to_dfrac_agree dq1 a ⋅ to_dfrac_agree dq2 b) ⊣⊢ ⌜✓ (dq1 ⋅ dq2)⌝ ∧ (a ≡ b).
    Proof.
      rewrite prod_validI /= internal_cmra_valid_discrete to_agree_op_validI //.
    Qed.

    Lemma frac_agree_validI q a : ✓ (to_frac_agree q a) ⊣⊢ ⌜(q ≤ 1)%Qp⌝.
    Proof.
      rewrite dfrac_agree_validI dfrac_valid_own //.
    Qed.

    Lemma frac_agree_validI_2 q1 q2 a b :
      ✓ (to_frac_agree q1 a ⋅ to_frac_agree q2 b) ⊣⊢ ⌜(q1 + q2 ≤ 1)%Qp⌝ ∧ (a ≡ b).
    Proof.
      rewrite dfrac_agree_validI_2 dfrac_valid_own //.
    Qed.
  End dfrac_agree.

  Section gmap_view.
    Context `{Countable K} {V : cmra}.
    Implicit Types (m : gmap K V) (k : K) (dq : dfrac) (v : V).

    Lemma gmap_view_both_dfrac_validI dp m k dq v :
      ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) ⊣⊢
      ∃ v' dq', ⌜✓ dp⌝ ∧ ⌜m !! k = Some v'⌝ ∧ ✓ (dq', v') ∧
                Some (dq, v) ≼ Some (dq', v').
    Proof. sbi_unfold=> n. apply: gmap_view_both_dfrac_validN. Qed.
    Lemma gmap_view_both_validI m dp k v :
      ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k (DfracOwn 1) v) ⊣⊢
      ⌜ ✓ dp ⌝ ∧ ✓ v ∧ m !! k ≡ Some v.
    Proof. sbi_unfold=> n. apply gmap_view_both_validN. Qed.
    Lemma gmap_view_both_validI_total `{!CmraTotal V} dp m k dq v :
      ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) ⊢
      ∃ v', ⌜✓ dp ⌝ ∧ ⌜ ✓ dq⌝ ∧ ⌜m !! k = Some v'⌝ ∧ ✓ v' ∧ v ≼ v'.
    Proof. sbi_unfold=> n. apply: gmap_view_both_dfrac_validN_total. Qed.

    Lemma gmap_view_frag_op_validI k dq1 dq2 v1 v2 :
      ✓ (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ⊣⊢
      ⌜✓ (dq1 ⋅ dq2)⌝ ∧ ✓ (v1 ⋅ v2).
    Proof. sbi_unfold=> n. apply gmap_view_frag_op_validN. Qed.
  End gmap_view.
End algebra.
