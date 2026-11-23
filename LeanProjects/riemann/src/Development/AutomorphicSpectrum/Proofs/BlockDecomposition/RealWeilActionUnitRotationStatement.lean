import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionUnitRotation
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
theorem _root_.GlobalTheory.T.real_weil_action_unit_rotation : ∀ (n : ℤ) (t : ℝ) (g : GL (Fin 2) ℝ) (x u : ℂ), ‖u‖ = 1 →
  piRc (chC n (Complex.I * t)) g (PhiInf n) (x * u) = u ^ (-n) * piRc (chC n (Complex.I * t)) g (PhiInf n) x := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.RealCircle.main | exact GlobalTheory.CompanionTheory.FexTheta.RealCircle.main | (intros; apply GlobalTheory.CompanionTheory.FexTheta.RealCircle.main <;> assumption)
