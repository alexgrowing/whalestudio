import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem exists_finset_clm_bound (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ (B : Finset V) (C : ℝ), 0 ≤ C ∧ ∀ (L : V →L[ℝ] ℂ) (X : V) (M : ℝ),
      (∀ Y ∈ B, ‖L Y‖ ≤ M) → 0 ≤ M → ‖L X‖ ≤ C * ‖X‖ * M := by
  classical
  obtain ⟨C, hC, h⟩ := (Module.finBasis ℝ V).exists_opNorm_le (F := ℂ)
  refine ⟨Finset.univ.image (Module.finBasis ℝ V), C, hC.le, fun L X M hB hM => ?_⟩
  have h1 : ‖L‖ ≤ C * M := h hM fun i => hB _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  calc ‖L X‖ ≤ ‖L‖ * ‖X‖ := L.le_opNorm X
    _ ≤ C * M * ‖X‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = C * ‖X‖ * M := by ring

theorem lieD_le_of_basis : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ (B : Finset (Lie E a)) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : GA E a → ℂ) (g : GA E a) (X : Lie E a) (M : ℝ), (∀ Y ∈ B, ‖lieD Y ψ g‖ ≤ M) → 0 ≤ M → ‖lieD X ψ g‖ ≤ C * ‖X‖ * M := by
  intro E _ _ _ a
  obtain ⟨B, C, hC, h⟩ := exists_finset_clm_bound (Lie E a)
  exact ⟨B, C, hC, fun ψ g X M hB hM => h (fderiv ℝ (chart ψ g) (oneL E a)) X M hB hM⟩

end GlobalTheory.CuspRapid
