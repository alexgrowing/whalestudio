import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaOneGammaZeroHomogeneousCocyclesFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaOneGammaZeroHomogeneousCocycles_finite : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → Module.Finite ℤ_[l] (Z1 N l w) := by
  first | exact @GlobalTheory.KZ.BettiB.module_finite_z1_padicInt | exact GlobalTheory.KZ.BettiB.module_finite_z1_padicInt | (intros; apply GlobalTheory.KZ.BettiB.module_finite_z1_padicInt <;> assumption)
