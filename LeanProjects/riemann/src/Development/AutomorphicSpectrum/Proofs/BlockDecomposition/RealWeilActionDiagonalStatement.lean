import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionDiagonal
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
theorem _root_.GlobalTheory.T.real_weil_action_diagonal : ∀ (n : ℤ) (t : ℝ) (z : ℂˣ) (a : ℝˣ), (a : ℝ) = ‖(z : ℂ)‖ ^ 2 → ∀ (g : GL (Fin 2) ℝ) (x : ℂ),
  piRc (chC n (Complex.I * t)) (dg2 a 1 * g) (PhiInf n) x =
    chC n (Complex.I * t) z * ((‖(z : ℂ)‖ : ℝ) : ℂ) * piRc (chC n (Complex.I * t)) g (PhiInf n) (x * z) := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.RealSim.piRc_sim | exact GlobalTheory.CompanionTheory.FexTheta.RealSim.piRc_sim | (intros; apply GlobalTheory.CompanionTheory.FexTheta.RealSim.piRc_sim <;> assumption)
