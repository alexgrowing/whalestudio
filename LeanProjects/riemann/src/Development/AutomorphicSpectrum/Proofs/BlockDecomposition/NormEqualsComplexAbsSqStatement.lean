import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormEqualsComplexAbsSq
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_equals_complex_abs_sq : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ κ : Kˣ,
  (((Units.map (Algebra.norm ℚ : K →* ℚ) κ : ℚˣ) : ℚ) : ℝ) = ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 ∧
  ((RationalIdeles.realPart (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) : ℝˣ) : ℝ) = ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.norm_eq_normSq_embU | exact GlobalTheory.CompanionTheory.FexTheta.norm_eq_normSq_embU | (intros; apply GlobalTheory.CompanionTheory.FexTheta.norm_eq_normSq_embU <;> assumption)
