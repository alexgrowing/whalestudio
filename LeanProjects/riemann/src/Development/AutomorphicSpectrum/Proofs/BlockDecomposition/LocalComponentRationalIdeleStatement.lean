import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComponentRationalIdele
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
theorem _root_.GlobalTheory.T.local_component_rational_idele : ∀ (v : Pl) (α : ℚˣ), ((Ad3.R.lc v (pri α) : (Qv v)ˣ) : Qv v) = (((α : ℚˣ) : ℚ) : Qv v) := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.lc_pri | exact GlobalTheory.CompanionTheory.FexTheta.lc_pri | (intros; apply GlobalTheory.CompanionTheory.FexTheta.lc_pri <;> assumption)
