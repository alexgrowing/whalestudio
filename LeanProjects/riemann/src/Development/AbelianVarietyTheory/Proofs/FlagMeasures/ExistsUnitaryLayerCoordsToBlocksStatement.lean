import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLayerCoordsToBlocks
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_layerCoords_to_blocks : ∀ (n m d : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), Biorth r m U (fun b => (U b)ᴴ) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) → (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) → (∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) → ∀ c : ℕ, ∃ Φ : ({i : Fin d // deg i = c} → ℂ) ≃ₗ[ℂ] (∀ b : Fin m, Fin (r b) → Fin (r (b + c + 1)) → ℂ), (∀ z, ∑ b, ∑ s, ∑ t, ‖Φ z b s t‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) ∧ ∀ Y ∈ lowers W c, ∀ b : Fin m, Matrix.of (Φ (fun i => (Y * (B i.1)ᴴ).trace) b) = (U b)ᴴ * Y * U (b + c + 1) := by
  first | exact @GlobalTheory.LayerIso.exists_layerIso | exact GlobalTheory.LayerIso.exists_layerIso | (intros; apply GlobalTheory.LayerIso.exists_layerIso <;> assumption)
