import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedPluriharmonicExtendsSmoothly
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4O
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_pluriharmonic_extends_smoothly : ∀ (e : ℕ) (M : Man e), M.FromSec → ∀ (σ : Fin (M.n + 1)) (Θ : LocPot (M.X σ)) (u : M.X σ → ℝ) (C : ℝ), IsPotential (M.A σ) Θ → (M.A σ).SmoothOn (M.Z σ)ᶜ u → (∀ j, ∀ y ∈ ((M.A σ).chart j).target, ((M.A σ).chart j).symm y ∉ M.Z σ → ∀ w, GlobalTheory.Mean4O.leviAt (M.A σ) (Θ + LocPot.ofFun u) j y w = 0) → (∀ x, x ∉ M.Z σ → |u x| ≤ C * Real.log (M.r σ x)) → ∃ g : M.X σ → ℝ, (M.A σ).Smooth g ∧ ∀ x, x ∉ M.Z σ → g x = u x := by
  first | exact @GlobalTheory.BdExtend.smooth_extension | exact GlobalTheory.BdExtend.smooth_extension | (intros; apply GlobalTheory.BdExtend.smooth_extension <;> assumption)
