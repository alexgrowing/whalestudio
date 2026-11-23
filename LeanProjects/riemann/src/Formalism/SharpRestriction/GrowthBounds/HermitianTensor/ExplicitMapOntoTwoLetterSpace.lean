import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Har4 Formalism.GradedWeylDivisibility MvPolynomial

theorem ta_sumToIter_rename_inr {R S₁ S₂ : Type} [CommRing R] (q : MvPolynomial S₂ R) :
    sumRingEquiv R S₁ S₂ (rename Sum.inr q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [rename_C, MvPolynomial.sumRingEquiv_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p n hp => rw [map_mul, map_mul, hp, rename_X, MvPolynomial.sumRingEquiv_X_inr, map_mul]

section A

variable (K : Type) [Field K] (m : ℕ)

theorem Psi_xs (f : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (rename Sum.inl f) = blockEmb K true (rename (fun i => (i, (0 : Fin (m + 1)))) f) := by
  simp only [PsiXY, blockEmb, aeval_rename, rename_rename]
  conv_rhs => rw [← aeval_X_left_apply ((rename _) f), aeval_rename]
  rfl

theorem Psi_ys (f : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (rename Sum.inr f) = blockEmb K false (aeval (covY K m) f) := by
  simp only [PsiXY, blockEmb, aeval_rename]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

end A

theorem explicit_map_injective : ExplicitMapInjective := by
  intro K _ m hm
  let Φ1 : PolXY K (m + 1) →ₐ[K] MvPolynomial (Fin (m + 1) ⊕ (Fin (m + 1) × Fin (m + 1))) K :=
    aeval (Sum.elim (fun i => X (Sum.inl i)) (fun i => rename Sum.inr (covY K m i)))
  let e : Fin (m + 1) ⊕ (Fin (m + 1) × Fin (m + 1)) → Bool × (Fin (m + 1) × Fin (m + 1)) :=
    Sum.elim (fun i => (true, (i, 0))) (fun v => (false, v))
  have he : Function.Injective e := by
    rintro (a | a) (b | b) h
    · simp only [e, Sum.elim_inl, Prod.mk.injEq, true_and, and_true] at h
      rw [h]
    · simp [e] at h
    · simp [e] at h
    · simp only [e, Sum.elim_inr, Prod.mk.injEq, true_and] at h
      rw [h]
  have hfac : PsiXY K m = (rename e).comp Φ1 := by
    apply algHom_ext
    rintro (i | i)
    · simp [PsiXY, Φ1, e]
    · simp only [PsiXY, Φ1, aeval_X, Sum.elim_inr, AlgHom.comp_apply, rename_rename]
      rfl
  have hφ : Function.Injective (aeval (covY K m) : MvPolynomial (Fin (m + 1)) K →ₐ[K] _) :=
    ShapeCovering.signed_minors_alg_independent K m hm
  have hcomm : (sumRingEquiv K (Fin (m + 1)) (Fin (m + 1) × Fin (m + 1))).toRingHom.comp Φ1.toRingHom =
      (map (aeval (covY K m) : MvPolynomial (Fin (m + 1)) K →ₐ[K] _).toRingHom).comp
        (sumRingEquiv K (Fin (m + 1)) (Fin (m + 1))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Φ1, sumRingEquiv_C]
    · rintro (i | i)
      · simp [Φ1, sumRingEquiv_X_inl]
      · simp [Φ1, ta_sumToIter_rename_inr, sumRingEquiv_X_inr]
  have h1 : Function.Injective Φ1 := by
    intro f1 f2 h
    have h2 := DFunLike.congr_fun hcomm f1
    have h3 := DFunLike.congr_fun hcomm f2
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe] at h2 h3
    rw [h, h3] at h2
    have h4 := map_injective _ hφ h2
    exact ((sumRingEquiv K (Fin (m + 1)) (Fin (m + 1))).injective h4).symm
  rw [hfac]
  exact (rename_injective e he).comp h1

theorem ta_isHom_prodX {A : Type} [CommRing A] {k : ℕ} (a : Fin k → ℕ) :
    (∏ i, X i ^ a i : MvPolynomial (Fin k) A).IsHomogeneous (∑ i, a i) := by
  exact IsHomogeneous.prod Finset.univ (fun i => X i ^ a i) a (fun i _ => isHomogeneous_X_pow i (a i))

theorem ta_monomial_split {K : Type} [Field K] {k : ℕ} (v : XY k →₀ ℕ) (c : K) :
    (monomial v c : PolXY K k) = c • (rename Sum.inl (∏ i : Fin k, X i ^ v (Sum.inl i)) *
      rename Sum.inr (∏ i : Fin k, X i ^ v (Sum.inr i))) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type, map_prod, map_prod,
    smul_eq_C_mul]
  simp only [map_pow, rename_X]

theorem ta_rename_inl_hom {K : Type} [Field K] {k P : ℕ} (f : MvPolynomial (Fin k) K) (h : f.IsHomogeneous P) :
    IsWeightedHomogeneous (wXY k) (rename Sum.inl f : PolXY K k) (P, 0) := by
  classical
  intro d hd
  have hmem : d ∈ (rename Sum.inl f : PolXY K k).support := mem_support_iff.2 hd
  rw [support_rename_of_injective Sum.inl_injective, Finset.mem_image] at hmem
  obtain ⟨d', hd', rfl⟩ := hmem
  have hP := h (mem_support_iff.1 hd')
  simp only [Finsupp.weight_apply] at hP ⊢
  rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  simp only [wXY, Sum.elim_inl]
  rw [← hP]
  ext
  · simp [Finsupp.sum, Prod.fst_sum]
  · simp [Finsupp.sum, Prod.snd_sum]

theorem ta_rename_inr_hom {K : Type} [Field K] {k Q : ℕ} (f : MvPolynomial (Fin k) K) (h : f.IsHomogeneous Q) :
    IsWeightedHomogeneous (wXY k) (rename Sum.inr f : PolXY K k) (0, Q) := by
  classical
  intro d hd
  have hmem : d ∈ (rename Sum.inr f : PolXY K k).support := mem_support_iff.2 hd
  rw [support_rename_of_injective Sum.inr_injective, Finset.mem_image] at hmem
  obtain ⟨d', hd', rfl⟩ := hmem
  have hQ := h (mem_support_iff.1 hd')
  simp only [Finsupp.weight_apply] at hQ ⊢
  rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]
  simp only [wXY, Sum.elim_inr]
  rw [← hQ]
  ext
  · simp [Finsupp.sum, Prod.fst_sum]
  · simp [Finsupp.sum, Prod.snd_sum]

theorem ta_mul_mem_PolAB {K : Type} [Field K] {k P Q : ℕ} (f1 f2 : MvPolynomial (Fin k) K)
    (h1 : f1.IsHomogeneous P) (h2 : f2.IsHomogeneous Q) :
    rename Sum.inl f1 * rename Sum.inr f2 ∈ PolAB K k P Q := by
  rw [Formalism.CountingSumsFrames.Har4.mem_PolAB_iff]
  have := (ta_rename_inl_hom f1 h1).mul (ta_rename_inr_hom f2 h2)
  simpa using this

theorem ta_nuOf_vec (m P : ℕ) (hm : 1 ≤ m) : nuOf (letterWt m P true) = fun t => if t = 0 then P else 0 := by
  funext t
  unfold nuOf letterWt
  simp only [if_true]
  have hl : Fin.last m ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [if_neg hl]
  split_ifs <;> simp

theorem ta_nuOf_cov (m Q : ℕ) : nuOf (letterWt m Q false) = fun t => if t = Fin.last m then 0 else Q := by
  funext t
  unfold nuOf letterWt
  simp only [Bool.false_eq_true, if_false, if_true]
  split_ifs <;> simp

theorem explicit_map_onto_two_letter_space : ExplicitMapOntoTwoLetters := by
  intro K _ m hm P Q x
  constructor
  · intro hx
    unfold twoSp tensorLat at hx
    refine Submodule.span_induction (p := fun x _ => ∃ f ∈ PolAB K (m + 1) P Q, PsiXY K m f = x) ?_
      ⟨0, Submodule.zero_mem _, map_zero _⟩ ?_ ?_ hx
    · rintro y ⟨F, hF, rfl⟩
      have ht := hF true
      have hf := hF false
      simp only [if_true, Bool.false_eq_true, if_false] at ht hf
      rw [ta_nuOf_vec m P hm] at ht
      rw [ta_nuOf_cov m Q] at hf
      obtain ⟨f1, h1, e1⟩ := (ShapeCovering.first_column_polynomials_characterize K m P (F true) hm).1 ht
      obtain ⟨f2, h2, e2⟩ := (ShapeCovering.signed_minor_polynomials_characterize K m Q (F false) hm).1 hf
      refine ⟨rename Sum.inl f1 * rename Sum.inr f2, ta_mul_mem_PolAB f1 f2 h1 h2, ?_⟩
      rw [covY_eq] at e2
      rw [map_mul, Psi_xs, Psi_ys, e1, e2, Fintype.prod_bool]
    · rintro x y _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      exact ⟨f + g, Submodule.add_mem _ hf hg, map_add _ _ _⟩
    · rintro c x _ ⟨f, hf, rfl⟩
      exact ⟨c • f, Submodule.smul_mem _ _ hf, map_smul _ _ _⟩
  · rintro ⟨f, hf, rfl⟩
    rw [f.as_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [ta_monomial_split, map_smul, map_mul, Psi_xs, Psi_ys]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨fun b : Bool => (cond b (rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1))))
        (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) K) ^ v (Sum.inl i)))
      (aeval (covY K m) (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) K) ^ v (Sum.inr i))) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), ?_, ?_⟩
    · intro b
      cases b
      · simp only [Bool.false_eq_true, if_false, cond_false]
        rw [ta_nuOf_cov m Q]
        refine (ShapeCovering.signed_minor_polynomials_characterize K m Q _ hm).2 ⟨_, ?_, rfl⟩
        have := ta_isHom_prodX (A := K) (fun i : Fin (m + 1) => v (Sum.inr i))
        rwa [show ∑ i : Fin (m + 1), v (Sum.inr i) = Q from (hf v hv).2] at this
      · simp only [if_true, cond_true]
        rw [ta_nuOf_vec m P hm]
        refine (ShapeCovering.first_column_polynomials_characterize K m P _ hm).2 ⟨_, ?_, rfl⟩
        have := ta_isHom_prodX (A := K) (fun i : Fin (m + 1) => v (Sum.inl i))
        rwa [show ∑ i : Fin (m + 1), v (Sum.inl i) = P from (hf v hv).1] at this
    · rw [Fintype.prod_bool]
      rfl

end Formalism.MainNotions.flipOneThree.Pf

end
