import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLocalThetaLocallyConstant
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_local_theta_locally_constant : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ g₀ : GL (Fin 2) (Qv v), L.plus g₀ → ∃ U ∈ nhds g₀, ∀ g ∈ U, ∀ (τ : (Qv v)ˣ) (ξ : K),
    (L.tw τ).val g ξ = (L.tw τ).val g₀ ξ := by
  first | exact @GlobalTheory.CompanionTheory.ThetaStab.val_stab | exact GlobalTheory.CompanionTheory.ThetaStab.val_stab | (intros; apply GlobalTheory.CompanionTheory.ThetaStab.val_stab <;> assumption)
