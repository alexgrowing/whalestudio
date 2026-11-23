import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularSSmul
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_modularS_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → sg c x (ModularGroup.S • τ) = sg c (act x ModularGroup.S) τ := by
  first | exact @GlobalTheory.Sieg.sg_S | exact GlobalTheory.Sieg.sg_S | (intros; apply GlobalTheory.Sieg.sg_S <;> assumption)
