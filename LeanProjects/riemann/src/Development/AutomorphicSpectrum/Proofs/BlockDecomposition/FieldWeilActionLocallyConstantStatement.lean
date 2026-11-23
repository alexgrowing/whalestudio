import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldWeilActionLocallyConstant
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_weil_action_locally_constant : GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
  ∀ c : Eˣ →* ℂˣ, IsUnit1 c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ g₀ : GL (Fin 2) F,
    (∃ t : Eˣ, Algebra.norm F (t : E) = (g₀.val).det) →
    ∃ U ∈ nhds g₀, ∀ g ∈ U, GL2LocalData.piE E χ σ η c g Φ = GL2LocalData.piE E χ σ η c g₀ Φ := by
  first | exact @GlobalTheory.CompanionTheory.WeilLocConst.piE_locConst | exact GlobalTheory.CompanionTheory.WeilLocConst.piE_locConst | (intros; apply GlobalTheory.CompanionTheory.WeilLocConst.piE_locConst <;> assumption)
