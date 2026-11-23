import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductCharacterNormOneTrivial
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldCoefficientNormOneTwistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionUnitRotationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFormulaGlobalCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormEqualsComplexAbsSqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicRealPartPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedStandardValuesAtIntegralStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_character_norm_one_trivial : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ g : G2, thT n t M g 0 ≠ 0 → ∀ κ ∈ K1 K, ∏ᶠ v, (M v).ct (k1 (M v) κ) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.TermZero.finprod_character_norm_one_eq_one | exact GlobalTheory.CompanionTheory.FexTheta.TermZero.finprod_character_norm_one_eq_one | (intros; apply GlobalTheory.CompanionTheory.FexTheta.TermZero.finprod_character_norm_one_eq_one <;> assumption)
