import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelModularSTransform
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddThetaProductSiegel_modularS_transform : ∀ (τ : ℍ) (z : ℂ), th (z / (τ : ℂ)) (ModularGroup.S • τ) = -Complex.I * ee (z ^ 2 / (2 * (τ : ℂ))) * th z τ := by
  first | exact @GlobalTheory.Sieg.ThInv.th_S | exact GlobalTheory.Sieg.ThInv.th_S | (intros; apply GlobalTheory.Sieg.ThInv.th_S <;> assumption)
