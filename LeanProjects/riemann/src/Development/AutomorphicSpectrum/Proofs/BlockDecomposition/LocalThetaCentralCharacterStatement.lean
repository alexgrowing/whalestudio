import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalThetaCentralCharacter
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
theorem _root_.GlobalTheory.T.local_theta_central_character : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → ¬ m.IsSp → ∀ (a : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)) (ξ : K), m.val (dg2 a a * g) ξ = omW m a * m.val g ξ := by
  first | exact @GlobalTheory.CompanionTheory.CenThetaNs.val_central | exact GlobalTheory.CompanionTheory.CenThetaNs.val_central | (intros; apply GlobalTheory.CompanionTheory.CenThetaNs.val_central <;> assumption)
