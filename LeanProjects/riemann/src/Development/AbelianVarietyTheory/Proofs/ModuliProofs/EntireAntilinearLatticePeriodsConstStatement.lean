import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EntireAntilinearLatticePeriodsConst
open Complex Matrix
open scoped ContDiff BigOperators Real
theorem _root_.GlobalTheory.T.entire_antilinear_lattice_periods_const : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v → (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) → t = 0 ∧ ∀ z, v z = v 0 := by
  first | exact @GlobalTheory.entire_antilinear_periods_const | exact GlobalTheory.entire_antilinear_periods_const | (intros; apply GlobalTheory.entire_antilinear_periods_const <;> assumption)
