import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionLocallyConstant
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_weil_action_locally_constant : GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ => ∀ c₁ : Fˣ →* ℂˣ, IsUnit1 c₁ → ∀ Φ ∈ GL2LocalData.SBE (F × F), ∀ g₀ : GL (Fin 2) F,
  ∃ U ∈ nhds g₀, ∀ g ∈ U, GL2LocalData.piS χ c₁ g Φ = GL2LocalData.piS χ c₁ g₀ Φ := by
  first | exact @GlobalTheory.CompanionTheory.SplitContG.piS_locConst | exact GlobalTheory.CompanionTheory.SplitContG.piS_locConst | (intros; apply GlobalTheory.CompanionTheory.SplitContG.piS_locConst <;> assumption)
