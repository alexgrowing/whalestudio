import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableLocalThetaCoefficient
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
theorem _root_.GlobalTheory.T.measurable_local_theta_coefficient : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K), Measurable (fL L g ξ) := by
  first | exact @GlobalTheory.CompanionTheory.FexThetaMeas.measurable_fL | exact GlobalTheory.CompanionTheory.FexThetaMeas.measurable_fL | (intros; apply GlobalTheory.CompanionTheory.FexThetaMeas.measurable_fL <;> assumption)
