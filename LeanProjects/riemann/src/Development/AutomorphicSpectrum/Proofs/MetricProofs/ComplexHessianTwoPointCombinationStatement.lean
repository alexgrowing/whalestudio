import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianTwoPointCombination
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_hessian_two_point_combination : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p₀ p₁ e₀ e₁ : ℂ)
    (B₀ B₁ : Matrix (Fin d) (Fin d) ℂ) (s t v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p₀ y) → ContDiffAt ℝ 2 f (Fin.cons p₁ y) → ContDiffAt ℝ 2 α y →
    hessC f (Fin.cons p₀ y) = blk e₀ B₀ → hessC f (Fin.cons p₁ y) = blk e₁ B₁ →
    hessC (fun z : Fin (d + 2) → ℂ => s * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        t * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + v * α (Fin.tail (Fin.tail z)))
      (Fin.cons p₀ (Fin.cons p₁ y)) =
    blk ((s : ℂ) * e₀) (blk ((t : ℂ) * e₁) ((s : ℂ) • B₀ + (t : ℂ) • B₁ + (v : ℂ) • hessC α y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_square | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_square | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_square <;> assumption)
