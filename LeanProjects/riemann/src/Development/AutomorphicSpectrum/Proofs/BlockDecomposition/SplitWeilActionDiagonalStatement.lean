import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionDiagonal
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
theorem _root_.GlobalTheory.T.split_weil_action_diagonal : GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ : Fˣ →* ℂˣ) (Φ : F × F → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
  ∀ (a : Fˣ) (g : GL (Fin 2) F) (x : F × F),
    GL2LocalData.piS χ c₁ (dg2 a 1 * g) Φ x = ((c₁ a : ℂˣ) : ℂ) * mp a (1 / 2) * GL2LocalData.piS χ c₁ g Φ ((a : F) * x.1, x.2) := by
  first | exact @GlobalTheory.CompanionTheory.SplitDiag.piS_diag | exact GlobalTheory.CompanionTheory.SplitDiag.piS_diag | (intros; apply GlobalTheory.CompanionTheory.SplitDiag.piS_diag <;> assumption)
