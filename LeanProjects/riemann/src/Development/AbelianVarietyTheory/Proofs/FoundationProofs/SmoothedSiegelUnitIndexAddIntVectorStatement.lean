import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitIndexAddIntVector
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_index_add_intVector : ∀ (c : ℕ) (x : Fin 2 → ℚ) (n : Fin 2 → ℤ) (τ : ℍ), admitted c x → sg c (fun i => x i + n i) τ = sg c x τ := by
  first | exact @GlobalTheory.Sieg.Per.sg_add_int | exact GlobalTheory.Sieg.Per.sg_add_int | (intros; apply GlobalTheory.Sieg.Per.sg_add_int <;> assumption)
