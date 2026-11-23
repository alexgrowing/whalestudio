import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtension

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

theorem UpperTheory.cm_inertia_restriction_holds : UpperTheory.V.Af.Cr.IneRes := by
  intro F₀ F Ω _ _ _ _ _ _ _ _ _ _
  classical
  unfold Ine IsPlaceOver Inertia
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hint : ∀ (A : ValuationSubring Ω) (x : Ω), IsIntegral ℤ x → A.valuation x ≤ 1 := by
    intro A x h
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (h.tower_top : IsIntegral A x)
    exact A.valuation_le_one y
  obtain ⟨α₁, hα₁⟩ := Field.exists_primitive_element F₀ F
  have hα₁alg : IsAlgebraic ℤ α₁ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (.of_finite ℚ α₁)
  obtain ⟨m, hm0, hmint⟩ := hα₁alg.exists_integral_multiple
  set α : F := m • α₁ with hαdef
  set g : Polynomial ℤ := minpoly ℤ α with hgdef
  set f : Polynomial F₀ := g.map (algebraMap ℤ F₀) with hfdef
  have hgmonic : g.Monic := minpoly.monic hmint
  have hfα : Polynomial.aeval α f = 0 := by
    rw [hfdef, Polynomial.aeval_map_algebraMap, hgdef, minpoly.aeval]
  have hfsep : f.Separable := by
    have h1 : (minpoly ℚ α).Separable := Algebra.IsSeparable.isSeparable ℚ α
    have h2 := h1.map (f := algebraMap ℚ F₀)
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hmint, Polynomial.map_map] at h2
    have h3 : (algebraMap ℚ F₀).comp (algebraMap ℤ ℚ) = algebraMap ℤ F₀ := RingHom.ext_int _ _
    rw [h3] at h2
    exact h2
  set c : F := Polynomial.aeval α (Polynomial.derivative f) with hcdef
  have hc0 : c ≠ 0 := hfsep.aeval_derivative_ne_zero hfα
  have hcint : IsIntegral ℤ c := by
    have h1 : c = Polynomial.aeval α (Polynomial.derivative g) := by
      rw [hcdef, hfdef, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
    have key := Polynomial.aeval_algHom_apply (integralClosure ℤ F).val
      (⟨α, hmint⟩ : integralClosure ℤ F) (Polynomial.derivative g)
    rw [h1]
    refine key ▸ ?_
    exact (Polynomial.aeval (⟨α, hmint⟩ : integralClosure ℤ F) (Polynomial.derivative g)).2
  set d : F₀ := Algebra.norm F₀ c with hddef
  have hdint : IsIntegral ℤ d := Algebra.isIntegral_norm F₀ hcint
  have hd0 : d ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc0
  set D : 𝓞 F₀ := ⟨d, hdint⟩ with hDdef
  have hD0 : D ≠ 0 := by
    intro h
    apply hd0
    exact congrArg (fun x : 𝓞 F₀ => (x : F₀)) h
  have hspan : Ideal.span {D} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hD0
  refine Filter.eventually_cofinite.mpr ((Ideal.finite_factors hspan).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hDv
  apply hv
  intro A hA σ hσ
  have hσ2 : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1 := hσ.2
  set α₀ : Ω := algebraMap F Ω α with hα₀def
  have h0 : Polynomial.aeval α₀ f = 0 := by
    rw [hα₀def, Polynomial.aeval_algebraMap_apply, hfα, map_zero]
  have hfix : σ α₀ = α₀ := by
    by_contra hne
    set fΩ : Polynomial Ω := f.map (algebraMap F₀ Ω) with hfΩ
    have hfΩ_monic : fΩ.Monic := (hgmonic.map _).map _
    have hfΩ0 : fΩ ≠ 0 := hfΩ_monic.ne_zero
    have hroot : ∀ y : Ω, Polynomial.aeval y f = 0 → y ∈ fΩ.roots := by
      intro y hy
      rw [Polynomial.mem_roots hfΩ0, Polynomial.IsRoot, hfΩ, Polynomial.eval_map_algebraMap]
      exact hy
    have hα₀root : α₀ ∈ fΩ.roots := hroot _ h0
    have hβroot : σ α₀ ∈ fΩ.roots := by
      apply hroot
      have := Polynomial.aeval_algHom_apply (σ : Ω ≃ₐ[F₀] Ω).toAlgHom α₀ f
      rw [h0, map_zero] at this
      exact this
    have hrootint : ∀ y ∈ fΩ.roots, IsIntegral ℤ y := by
      intro y hy
      refine ⟨g, hgmonic, ?_⟩
      rw [Polynomial.mem_roots hfΩ0, Polynomial.IsRoot, hfΩ, hfdef, Polynomial.map_map,
        ← Polynomial.eval₂_eq_eval_map] at hy
      have hZ : algebraMap ℤ Ω = (algebraMap F₀ Ω).comp (algebraMap ℤ F₀) := RingHom.ext_int _ _
      rw [hZ]
      exact hy
    have hder : algebraMap F Ω c = ((fΩ.roots.erase α₀).map (α₀ - ·)).prod := by
      rw [← (IsAlgClosed.splits fΩ).eval_root_derivative hfΩ_monic hα₀root]
      rw [hfΩ, Polynomial.derivative_map, Polynomial.eval_map_algebraMap, hcdef, hα₀def,
        Polynomial.aeval_algebraMap_apply]
    have hβmem : σ α₀ ∈ fΩ.roots.erase α₀ := (Multiset.mem_erase_of_ne hne).mpr hβroot
    have hcv : A.valuation (algebraMap F Ω c) < 1 := by
      rw [hder, ← Multiset.cons_erase hβmem, Multiset.map_cons, Multiset.prod_cons, Valuation.map_mul]
      have h1 : A.valuation (α₀ - σ α₀) < 1 := by
        rw [Valuation.map_sub_swap]
        exact hσ2 α₀ (hint A α₀ (hrootint α₀ hα₀root))
      have h2 : A.valuation (((fΩ.roots.erase α₀).erase (σ α₀)).map (α₀ - ·)).prod ≤ 1 := by
        apply hint
        apply IsIntegral.multiset_prod
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
        exact (hrootint α₀ hα₀root).sub
          (hrootint y (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hy)))
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) h1
    have hnorm := Algebra.norm_eq_prod_embeddings F₀ Ω c
    set φ₀ : F →ₐ[F₀] Ω := IsScalarTower.toAlgHom F₀ F Ω with hφ₀
    rw [← Finset.mul_prod_erase Finset.univ (fun φ : F →ₐ[F₀] Ω => φ c) (Finset.mem_univ φ₀)] at hnorm
    have hdv : A.valuation (algebraMap F₀ Ω d) < 1 := by
      rw [hddef, hnorm, Valuation.map_mul]
      have h2 : A.valuation (∏ φ ∈ Finset.univ.erase φ₀, φ c) ≤ 1 := by
        apply hint
        apply IsIntegral.prod
        intro φ _
        exact hcint.map φ.toRingHom.toIntAlgHom
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) hcv
    exact hDv ((hA D).mp hdv)
  have hfix1 : σ (algebraMap F Ω α₁) = algebraMap F Ω α₁ := by
    have h : σ (algebraMap F Ω α) = algebraMap F Ω α := hfix
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
    simp only [hαdef, zsmul_eq_mul, map_mul, map_intCast] at h
    exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hm0) h
  have hφ : ((σ : Ω ≃ₐ[F₀] Ω).toAlgHom).comp (IsScalarTower.toAlgHom F₀ F Ω) =
      IsScalarTower.toAlgHom F₀ F Ω := by
    have hadj : Algebra.adjoin F₀ {α₁} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic α₁), hα₁, IntermediateField.top_toSubalgebra]
    refine AlgHom.ext_of_adjoin_eq_top hadj ?_
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hfix1
  have hcomm : ∀ y : F, σ (algebraMap F Ω y) = algebraMap F Ω y := fun y => DFunLike.congr_fun hφ y
  refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[F₀] Ω).toRingEquiv) hcomm, ?_⟩
  ext x
  rfl
