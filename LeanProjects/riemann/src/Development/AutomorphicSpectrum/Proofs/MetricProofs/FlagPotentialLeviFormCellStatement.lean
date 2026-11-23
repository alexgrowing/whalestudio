import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialLeviFormCell
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_potential_levi_form_cell : ∀ (N j : ℕ), j ≤ N → ∀ (i : Fin N) (w : Pairs N → ℂ), let r : Fin N → ℕ := fun a => if (a : ℕ) < N - j then j + a else a - (N - j); ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 ∧ levi (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 w = ∑ p : Pairs N, if min (r p.1.1) (r p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (r p.1.1) (r p.1.2) then (1 / 2 : ℝ) * ‖w p‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell | exact GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell <;> assumption)
