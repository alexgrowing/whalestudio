import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory

theorem isCuspForm_of_conj_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a), (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) → (∀ o φ, act o (C φ) = C (act o φ)) → (∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ)) → ∀ φ : Sm E a, IsCuspForm φ → IsCuspForm (C φ) := by
  intro E _ _ _ a C hC hact hZ φ hφ
  obtain ⟨h, hc⟩ := hφ
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro γ g
    rw [hC, hC, h.left]
  · convert h.level using 1
    ext k
    change act (.fin k) (C φ) = C φ ↔ act (.fin k) φ = φ
    rw [hact]
    exact C.injective.eq_iff
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      C.toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (hact (.cpt k) φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map C.toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := hZ z hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  · intro g
    obtain ⟨K, N, h1⟩ := h.growth g
    refine ⟨K, N, fun y => ?_⟩
    rw [hC, RCLike.norm_conj]
    exact h1 y
  · intro r hr0 hra _ _ μ 𝓕 hμ h𝓕 g
    have := hc r hr0 hra μ 𝓕 hμ h𝓕 g
    simp_rw [hC]
    rw [integral_conj, this, map_zero]

end GlobalTheory
