import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLocalCentralScalarsEqOne
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_local_central_scalars_eq_one : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → ∀ (a : (Qv v)ˣ), ‖omW m a‖ = 1 ∧ ‖om0 m a‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CenTheta.norm_central_scalars_eq_one | exact GlobalTheory.CompanionTheory.CenTheta.norm_central_scalars_eq_one | (intros; apply GlobalTheory.CompanionTheory.CenTheta.norm_central_scalars_eq_one <;> assumption)
