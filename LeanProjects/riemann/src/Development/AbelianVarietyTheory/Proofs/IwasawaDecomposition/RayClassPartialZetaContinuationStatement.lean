import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassPartialZetaContinuation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_partial_zeta_continuation : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ D : RayData K M, ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : D.G, ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = ρ ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → LSeriesSummable (D.cnt c) s ∧ Z s = (s - 1) * LSeries (D.cnt c) s := by
  first | exact @GlobalTheory.Mem.PartialZeta.partial_zeta_continuation | exact GlobalTheory.Mem.PartialZeta.partial_zeta_continuation | (intros; apply GlobalTheory.Mem.PartialZeta.partial_zeta_continuation <;> assumption)
