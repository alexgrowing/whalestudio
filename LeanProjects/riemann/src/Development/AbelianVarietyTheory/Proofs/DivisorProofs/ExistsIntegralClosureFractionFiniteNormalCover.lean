import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
open AlgebraicGeometry CategoryTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Geo.Tor

open GlobalTheory.Poinc.FinPts in

theorem GlobalTheory.Poinc.exists_div_integralClosure_of_mem_O : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (z₁ : M₁.Z) (z₂ : M₂.Z), q z₂ = z₁ → letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q _ hF hg z₁ z₂ hq x hx
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  have halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x) := fun _ => rfl
  haveI := hF
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial
  have hz₂ : z₂ ∈ q ⁻¹ᵁ U := show q z₂ ∈ U by rw [hq]; exact hz
  obtain ⟨c, hc, d, hd, hd0, hdinv, e⟩ := GlobalTheory.T.exists_fraction_ringOn_of_mem_modelLocalRing _ _ M₂ _ (hU.preimage q) z₂ hz₂ x hx
  exact ⟨c, (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hc), d,
    (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hd), hd0, hdinv, e⟩
