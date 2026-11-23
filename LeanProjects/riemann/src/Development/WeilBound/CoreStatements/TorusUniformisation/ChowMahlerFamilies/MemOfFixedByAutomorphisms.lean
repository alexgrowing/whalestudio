import Mathlib
import Mathlib
open NumberField IsDedekindDomain

namespace PositivityTheory.Xgn.FixedFieldAutomorphism

open scoped Cardinal

theorem exists_equiv {R K L : Type} [CommRing R] [IsDomain R] [Field K] [Field L]
    [IsAlgClosed K] [IsAlgClosed L] [Algebra R K] [Algebra R L] [FaithfulSMul R K]
    [FaithfulSMul R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ g : K ≃+* L, ∀ r, g (algebraMap R K r) = algebraMap R L r := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR
    (hKL ▸ hK)
  have h3 : #s = #t := by rw [← h1, ← h2, hKL]
  obtain ⟨e⟩ := Cardinal.eq.1 h3
  haveI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  haveI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e' : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e'.toRingEquiv, fun r => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap,
    IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : t → L))) L]
  congr 1
  exact e'.commutes r

theorem exists_aut {R : Type} [CommRing R] [IsDomain R] (hR : #R ≤ ℵ₀) (i j : R →+* ℂ)
    (hi : Function.Injective i) (hj : Function.Injective j) :
    ∃ g : ℂ ≃+* ℂ, ∀ r, g (i r) = j r := by
  have hC : ℵ₀ < #ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  exact @exists_equiv R ℂ ℂ _ _ _ _ _ _ i.toAlgebra j.toAlgebra
    ((@faithfulSMul_iff_algebraMap_injective R ℂ _ _ i.toAlgebra).2 hi)
    ((@faithfulSMul_iff_algebraMap_injective R ℂ _ _ j.toAlgebra).2 hj) hR hC rfl

end PositivityTheory.Xgn.FixedFieldAutomorphism

theorem PositivityTheory.Xgn.mem_of_fixed_by_automorphisms : ∀ (F : IntermediateField ℚ ℂ) (c : ℂ), FiniteDimensional ℚ F → (∀ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) → g c = c) → c ∈ F := by
  intro F c hF h
  have hFc : Cardinal.mk F ≤ Cardinal.aleph0 := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ F
    simpa using this
  by_cases hc : IsAlgebraic F c
  · have hint : IsIntegral F c := hc.isIntegral
    haveI : FiniteDimensional F (IntermediateField.adjoin F {c}) :=
      IntermediateField.adjoin.finiteDimensional hint
    have hE : Cardinal.mk (IntermediateField.adjoin F {c}) ≤ Cardinal.aleph0 := by
      refine (Algebra.IsAlgebraic.cardinalMk_le_max F _).trans (max_le hFc le_rfl)
    have key : ∀ φ : IntermediateField.adjoin F {c} →ₐ[F] ℂ,
        φ = (IntermediateField.adjoin F {c}).val := by
      intro φ
      obtain ⟨g, hg⟩ := PositivityTheory.Xgn.FixedFieldAutomorphism.exists_aut hE
        (IntermediateField.adjoin F {c}).val.toRingHom φ.toRingHom
        (RingHom.injective _) (RingHom.injective _)
      have h1 : g c = c := h g fun a ha => by
        have := hg (algebraMap F _ ⟨a, ha⟩)
        simpa using this
      have h2 := hg (IntermediateField.AdjoinSimple.gen F c)
      refine (IntermediateField.adjoin.powerBasis hint).algHom_ext ?_
      rw [IntermediateField.adjoin.powerBasis_gen]
      exact h2.symm.trans h1
    have hcard := AlgHom.card F (IntermediateField.adjoin F {c}) ℂ
    have h1 : Module.finrank F (IntermediateField.adjoin F {c}) = 1 := by
      rw [← hcard, Fintype.card_eq_one_iff]
      exact ⟨_, key⟩
    have h2 : c ∈ (⊥ : IntermediateField F ℂ) :=
      IntermediateField.finrank_adjoin_simple_eq_one_iff.1 h1
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 h2
    exact a.2
  · exfalso
    have hc' : ¬ IsAlgebraic F (c + 1) := fun h' => hc (by
      have := h'.isIntegral.sub (isIntegral_one (R := F))
      simpa using this.isAlgebraic)
    have hP : Cardinal.mk (Polynomial F) ≤ Cardinal.aleph0 :=
      Polynomial.cardinalMk_le_max.trans (max_le hFc le_rfl)
    obtain ⟨g, hg⟩ := PositivityTheory.Xgn.FixedFieldAutomorphism.exists_aut hP
      (Polynomial.aeval (R := F) c).toRingHom (Polynomial.aeval (R := F) (c + 1)).toRingHom
      (transcendental_iff_injective.1 hc) (transcendental_iff_injective.1 hc')
    have h1 : g c = c := h g fun a ha => by
      have := hg (Polynomial.C ⟨a, ha⟩)
      simpa using this
    have h2 := hg Polynomial.X
    simp [h1] at h2
