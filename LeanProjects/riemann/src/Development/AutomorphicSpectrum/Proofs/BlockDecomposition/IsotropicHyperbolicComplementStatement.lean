import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicHyperbolicComplement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_hyperbolic_complement : ∀ {n D : ℕ} (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin D) ℂ), Cᴴ * C = 1 → Cᴴ * Formalism.REAL.Jm ε * C = 0 → ∃ (m : ℕ) (R : Matrix (Fin n) (Fin m) ℂ) (ε' : Fin m → Bool), Rᴴ * R = 1 ∧ Formalism.REAL.Jm ε * R = R * Formalism.REAL.Jm ε' ∧ Cᴴ * R = 0 ∧ C * Cᴴ + Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε + R * Rᴴ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame | exact GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame | (intros; apply GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame <;> assumption)
