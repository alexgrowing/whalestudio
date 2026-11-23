import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagOrthonormalAdaptedBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_orthonormal_adapted_basis : ∀ {n a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ → Monotone W → ∃ (D : ℕ) (C : Matrix (Fin n) (Fin D) ℂ) (τ : Fin D → ℕ), Cᴴ * C = 1 ∧ Monotone τ ∧ (∀ c, τ c < a) ∧ ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i ↔ ∃ v : Fin D → ℂ, y = C *ᵥ v ∧ ∀ c, (i : ℕ) ≤ τ c → v c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Flag.exists_flag_frame | exact GlobalTheory.CompanionTheory.Flag.exists_flag_frame | (intros; apply GlobalTheory.CompanionTheory.Flag.exists_flag_frame <;> assumption)
