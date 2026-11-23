import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem modelAt_shortTwist_four_mul_add_one : ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ D : ℂ) (k : ℤ), a₄ ∈ F → a₆ ∈ F → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D → ModelAt V F (shortTwist (4 * (k : ℂ) + 1) a₄ a₆) ((4 * (k : ℂ) + 1) ^ 6 * D) := by
  intro V F a₄ a₆ D k _ _ h
  obtain ⟨C, hu, hr, hs, ht, ⟨h1, h2, h3, h4, h6⟩, hΔ⟩ := h
  set d : ℂ := 4 * (k : ℂ) + 1 with hd
  have hkV : (k : ℂ) ∈ V := intCast_mem V k
  have hdV : d ∈ V := add_mem (mul_mem (by exact_mod_cast intCast_mem V 4 : (4 : ℂ) ∈ V) hkV) (one_mem V)
  have hkF : (k : ℂ) ∈ F := by simpa using IntermediateField.intCast_mem F k
  have hdF : d ∈ F := F.add_mem (F.mul_mem (by simpa using IntermediateField.intCast_mem F 4) hkF) F.one_mem
  let W₀ : WeierstrassCurve ℂ := ⟨0, 0, 0, a₄, a₆⟩
  let C' : VariableChange ℂ := ⟨C.u, d * C.r, C.s, d * C.t⟩
  refine ⟨C', hu, F.mul_mem hdF hr, hs, F.mul_mem hdF ht, ?_, ?_⟩
  · have e1 : (C' • shortTwist d a₄ a₆).a₁ = (C • W₀).a₁ := by
      simp only [variableChange_a₁, shortTwist, W₀, C']
    have e2 : (C' • shortTwist d a₄ a₆).a₂ = d * (C • W₀).a₂ + k * (C • W₀).a₁ ^ 2 := by
      simp only [variableChange_a₁, variableChange_a₂, shortTwist, W₀, C', hd]; ring
    have e3 : (C' • shortTwist d a₄ a₆).a₃ = d * (C • W₀).a₃ := by
      simp only [variableChange_a₃, shortTwist, W₀, C']; ring
    have e4 : (C' • shortTwist d a₄ a₆).a₄ = d ^ 2 * (C • W₀).a₄ + 2 * k * d * (C • W₀).a₁ * (C • W₀).a₃ := by
      simp only [variableChange_a₁, variableChange_a₃, variableChange_a₄, shortTwist, W₀, C', hd]; ring
    have e6 : (C' • shortTwist d a₄ a₆).a₆ = d ^ 3 * (C • W₀).a₆ + k * d ^ 2 * (C • W₀).a₃ ^ 2 := by
      simp only [variableChange_a₃, variableChange_a₆, shortTwist, W₀, C', hd]; ring
    have h2V : (2 : ℂ) ∈ V := by simpa using intCast_mem V 2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e1]; exact h1
    · rw [e2]; exact add_mem (mul_mem hdV h2) (mul_mem hkV (pow_mem h1 2))
    · rw [e3]; exact mul_mem hdV h3
    · rw [e4]; exact add_mem (mul_mem (pow_mem hdV 2) h4)
        (mul_mem (mul_mem (mul_mem (mul_mem h2V hkV) hdV) h1) h3)
    · rw [e6]; exact add_mem (mul_mem (pow_mem hdV 3) h6)
        (mul_mem (mul_mem hkV (pow_mem hdV 2)) (pow_mem h3 2))
  · have eΔ : (C' • shortTwist d a₄ a₆).Δ = d ^ 6 * (C • W₀).Δ := by
      rw [variableChange_Δ, variableChange_Δ]
      simp only [C', W₀, shortTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [eΔ, map_mul, map_mul, hΔ]

end GlobalTheory.CMModel
