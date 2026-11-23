import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldWeilActionDiagonal
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
theorem _root_.GlobalTheory.T.field_weil_action_diagonal : GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (c : Eˣ →* ℂˣ), ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ (t : Eˣ) (a : Fˣ),
  (a : F) = Algebra.norm F (t : E) → ∀ (g : GL (Fin 2) F) (x : E),
    GL2LocalData.piE E χ σ η c (dg2 a 1 * g) Φ x = ((c t : ℂˣ) : ℂ) * mp a (1 / 2) * GL2LocalData.piE E χ σ η c g Φ (x * t) := by
  first | exact @GlobalTheory.CompanionTheory.PieDiag.piE_diag | exact GlobalTheory.CompanionTheory.PieDiag.piE_diag | (intros; apply GlobalTheory.CompanionTheory.PieDiag.piE_diag <;> assumption)
