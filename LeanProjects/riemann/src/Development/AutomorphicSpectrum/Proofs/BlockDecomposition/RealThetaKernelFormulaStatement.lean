import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealThetaKernelFormula
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_theta_kernel_formula : ∀ (n : ℤ) (a b c d r : ℝ), 0 < r → a * d - b * c = 1 → ∀ z : ℂ,
  rWR a b c d (fun y => PhiInf n (y * r)) z =
    (r : ℂ) ^ n.natAbs * ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
      (if 0 ≤ n then (starRingEnd ℂ) z ^ n.natAbs else z ^ n.natAbs) *
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) /
        ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2))) * ((Complex.normSq z : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.RealTh.GForm.gform | exact GlobalTheory.CompanionTheory.RealTh.GForm.gform | (intros; apply GlobalTheory.CompanionTheory.RealTh.GForm.gform <;> assumption)
