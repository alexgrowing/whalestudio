import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearZeroOfKillsTranslatesTensor
import Mathlib
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinear_zero_of_kills_translates_tensor : ∀ (ι : Type) [Fintype ι] (H : ι → Type) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)] (G : ι → Type) [∀ i, Group (G i)] (π : ∀ i, G i →* (H i →L[ℂ] H i)), (∀ i g x, ‖π i g x‖ = ‖x‖) → (∀ i, ∀ B : H i →L[ℂ] H i, (∀ g, B.comp (π i g) = (π i g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ (H i)) → ∀ (Sm : ∀ i, Submodule ℂ (H i)), (∀ i, Dense (Sm i : Set (H i))) → ∀ (hinv : ∀ i g, ∀ x ∈ Sm i, π i g x ∈ Sm i) (L : MultilinearMap ℂ (fun i => Sm i) ℂ) (C : ℝ), (∀ v, ‖L v‖ ≤ C * ∏ i, ‖(v i : H i)‖) → ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → ∀ i, Sm i), (∀ g : ∀ i, G i, ∑ j, c j * L (fun i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩) = 0) → ∀ (φ : ∀ i, H i) (u : ∀ i, Sm i), (∑ j, c j * ∏ i, ⟪φ i, (v j i : H i)⟫_ℂ) * L u = 0 := by
  first | exact @GlobalTheory.DensityMultiPlace.multilinear_translates_zero | exact GlobalTheory.DensityMultiPlace.multilinear_translates_zero | (intros; apply GlobalTheory.DensityMultiPlace.multilinear_translates_zero <;> assumption)
