import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.BridgeDefs

namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

open Polynomial in
private theorem minpoly_map_eq_prod_gal {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (x : L) (hx : Algebra.adjoin F {x} = ⊤) :
    (minpoly F x).map (algebraMap F L) = ∏ σ : Gal(L/F), (X - C (σ x)) := by
  classical
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hinj : Function.Injective (fun σ : Gal(L/F) => σ x) := by
    intro σ τ h
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top hx
    rintro y rfl
    exact h
  have hm : (∏ σ : Gal(L/F), (X - C (σ x))).Monic :=
    monic_prod_of_monic _ _ fun σ _ => monic_X_sub_C _
  have hdvd : (∏ σ : Gal(L/F), (X - C (σ x))) ∣ (minpoly F x).map (algebraMap F L) := by
    apply Finset.prod_dvd_of_coprime
    · intro σ _ τ _ hne
      exact pairwise_coprime_X_sub_C hinj hne
    · intro σ _
      rw [dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap, aeval_algEquiv]
      simp
  refine eq_of_monic_of_dvd_of_natDegree_le hm ((minpoly.monic hint).map _) hdvd ?_
  rw [natDegree_map, natDegree_prod_of_monic _ _ (fun σ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  exact minpoly.natDegree_le x

open Polynomial Classical in
private theorem aeval_derivative_minpoly_eq_prod_gal {F L : Type*} [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L] (x : L)
    (hx : Algebra.adjoin F {x} = ⊤) :
    aeval x (derivative (minpoly F x)) = ∏ σ ∈ (Finset.univ : Finset Gal(L/F)).erase 1, (x - σ x) := by
  rw [← eval_map_algebraMap, ← derivative_map, minpoly_map_eq_prod_gal x hx,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : Gal(L/F))), derivative_mul]
  simp [eval_prod]

open Polynomial Classical in
private theorem differentIdeal_eq_span_of_prod (A F : Type*) {L : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field F] [Field L] [NumberField L] [Algebra A F] [IsFractionRing A F]
    [Algebra F L] [Algebra A L] [Algebra A (𝓞 L)] [IsScalarTower A F L] [IsScalarTower A (𝓞 L) L]
    [IsIntegralClosure (𝓞 L) A L] [Module.IsTorsionFree A (𝓞 L)]
    [FiniteDimensional F L] [IsGalois F L] (x y : 𝓞 L)
    (hx : Algebra.adjoin A {x} = ⊤) (hx' : Algebra.adjoin F {algebraMap (𝓞 L) L x} = ⊤)
    (hy : algebraMap (𝓞 L) L y = ∏ σ ∈ (Finset.univ : Finset Gal(L/F)).erase 1,
      (algebraMap (𝓞 L) L x - σ (algebraMap (𝓞 L) L x))) :
    differentIdeal A (𝓞 L) = Ideal.span {y} := by
  have h := conductor_mul_differentIdeal A F L x hx'
  rw [conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul] at h
  rw [h]
  congr 2
  apply IsFractionRing.injective (𝓞 L) L
  have hint : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  rw [hy, ← aeval_derivative_minpoly_eq_prod_gal _ hx',
    minpoly.isIntegrallyClosed_eq_field_fractions F L hint, derivative_map, aeval_map_algebraMap,
    aeval_algebraMap_apply]

private theorem adjoin_root_eq_top (E : Type*) [Field E] [Algebra ℚ E] [Algebra E K]
    [IsScalarTower ℚ E K] {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    Algebra.adjoin E {ζ} = ⊤ := by
  have h := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := ℚ) hζ
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Algebra.adjoin ℚ {ζ} := h ▸ Algebra.mem_top
  have : Algebra.adjoin ℚ {ζ} ≤ (Algebra.adjoin E {ζ}).restrictScalars ℚ :=
    Algebra.adjoin_le (by simp)
  exact this hy

private theorem adjoin_toInteger_eq_top (A : Type*) [CommRing A] [Algebra A (𝓞 K)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    Algebra.adjoin A {hζ.toInteger} = ⊤ := by
  have h := adjoin_singleton_eq_top hζ
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Algebra.adjoin ℤ {hζ.toInteger} := h ▸ Algebra.mem_top
  have : Algebra.adjoin ℤ {hζ.toInteger} ≤ (Algebra.adjoin A {hζ.toInteger}).restrictScalars ℤ :=
    Algebra.adjoin_le (by simp)
  exact this hy

open Classical in

theorem relDifferent_eq_span_prod (E : IntermediateField ℚ K) {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    differentIdeal (𝓞 E) (𝓞 K) = Ideal.span
      {∏ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∈ E.fixingSubgroup ∧ σ ≠ 1),
        (hζ.toInteger - σ • hζ.toInteger)} := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  refine differentIdeal_eq_span_of_prod (𝓞 E) E hζ.toInteger _
    (adjoin_toInteger_eq_top _ hζ) (adjoin_root_eq_top E hζ) ?_
  rw [map_prod]
  symm
  refine Finset.prod_bij (fun σ _ => σ.restrictScalars ℚ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    · intro h
      apply (Finset.mem_erase.mp hσ).1
      ext x
      exact DFunLike.congr_fun h x
  · intro σ _ τ _ h
    ext x
    exact DFunLike.congr_fun h x
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨E.fixingSubgroupEquiv ⟨σ, hσ.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro h
      apply hσ.2
      ext x
      exact DFunLike.congr_fun h x
    · rfl
  · intro σ _
    rfl

open Classical in

theorem map_differentIdeal_eq_span_prod (E : IntermediateField ℚ K) {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) :
    (differentIdeal ℤ (𝓞 E)).map (algebraMap (𝓞 E) (𝓞 K)) = Ideal.span
      {∏ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∉ E.fixingSubgroup),
        (hζ.toInteger - σ • hζ.toInteger)} := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  have h1 : differentIdeal ℤ (𝓞 K) = Ideal.span
      {∏ σ ∈ (Finset.univ : Finset Gal(K/ℚ)).erase 1, (hζ.toInteger - σ • hζ.toInteger)} := by
    refine differentIdeal_eq_span_of_prod ℤ ℚ hζ.toInteger _
      (adjoin_toInteger_eq_top _ hζ) (adjoin_root_eq_top ℚ hζ) ?_
    rw [map_prod]
    rfl
  have h2 := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 K)
  have h3 : differentIdeal (𝓞 E) (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  apply mul_left_cancel₀ h3
  rw [← h2, h1, relDifferent_eq_span_prod E hζ, Ideal.span_singleton_mul_span_singleton,
    ← Finset.prod_filter_mul_prod_filter_not _ (fun σ : Gal(K/ℚ) => σ ∈ E.fixingSubgroup)]
  congr 4
  · ext σ
    simp [and_comm]
  · ext σ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and,
      and_iff_right_iff_imp]
    rintro h rfl
    exact h (one_mem _)

end KStar.Ram
