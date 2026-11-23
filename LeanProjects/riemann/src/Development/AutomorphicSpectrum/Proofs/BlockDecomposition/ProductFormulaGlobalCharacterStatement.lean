import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFormulaGlobalCharacter
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
theorem _root_.GlobalTheory.T.product_formula_global_character : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, (∀ v, (M v).ok) → ∀ κ : Kˣ,
    (Function.mulSupport fun v : Pl => cW (M v) κ).Finite ∧
      (∏ᶠ v : Pl, cW (M v) κ) * chC n (Complex.I * t) (embU κ) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.HeckeUnit.cW_finprod_mul_chC | exact GlobalTheory.CompanionTheory.FexTheta.HeckeUnit.cW_finprod_mul_chC | (intros; apply GlobalTheory.CompanionTheory.FexTheta.HeckeUnit.cW_finprod_mul_chC <;> assumption)
