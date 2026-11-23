import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.FunctionalEquationGL2GL1Complex
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchwartzSlice

open Ad3.K.LC Ad3.K.LC.C

noncomputable def sliceMap (X : M23) : (Fin 2 → ℂ) → M23 × (Fin 2 → ℂ) := fun q => (X, q)

theorem sliceMap_temperate (X : M23) : (sliceMap X).HasTemperateGrowth := by
  have h : sliceMap X = fun q => (X, (0 : Fin 2 → ℂ)) + (ContinuousLinearMap.inr ℝ M23 (Fin 2 → ℂ)) q := by
    funext q
    simp [sliceMap]
  rw [h]
  exact (Function.HasTemperateGrowth.const _).add (ContinuousLinearMap.inr ℝ M23 (Fin 2 → ℂ)).hasTemperateGrowth

theorem sliceMap_upper (X : M23) :
    ∃ (k : ℕ) (C : ℝ), ∀ q, ‖q‖ ≤ C * (1 + ‖sliceMap X q‖) ^ k := by
  refine ⟨1, 1, fun q => ?_⟩
  have h : ‖q‖ ≤ ‖sliceMap X q‖ := by
    simp only [sliceMap, Prod.norm_def]
    exact le_max_right _ _
  simp only [pow_one, one_mul]
  linarith

theorem slices_schwartz : Ad3.K.LC.C.SlS := by
  intro Ψ X
  refine ⟨SchwartzMap.compCLM ℂ (sliceMap_temperate X) (sliceMap_upper X) Ψ, ?_⟩
  funext q
  rfl

end GlobalTheory.CompanionTheory.SchwartzSlice
