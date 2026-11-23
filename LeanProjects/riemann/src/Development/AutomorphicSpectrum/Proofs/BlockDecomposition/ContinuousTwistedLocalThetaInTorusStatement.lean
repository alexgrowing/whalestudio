import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousTwistedLocalThetaInTorus
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_twisted_local_theta_in_torus : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ g₀ : GL (Fin 2) (Qv v), L.plus g₀ → ∀ ξ : K, Continuous (fun τ : (Qv v)ˣ => (L.tw τ).val g₀ ξ) := by
  first | exact @GlobalTheory.CompanionTheory.TwistCont.val_tw_continuous | exact GlobalTheory.CompanionTheory.TwistCont.val_tw_continuous | (intros; apply GlobalTheory.CompanionTheory.TwistCont.val_tw_continuous <;> assumption)
