import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEntireGeneratorDivFrames
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_entire_ne_zero_val_eq_mul_prod_frames : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), L.IsLB → ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ A.left)) (ep : K → ℤ) (t : LB.Gen (LB.LinComb L φ ep)), t.IsGen → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (pt : E → (Sp ℂ ⟶ Y)) (z : K → E → Fin g → ℂ), GlobalTheory.PowUnif.IsHolFamily pt → (∀ k, Differentiable ℂ (z k)) → (∀ e k, pt e ≫ φ k = (u.ex (z k e)).left) → ∃ T : E → ℂ, Differentiable ℂ T ∧ (∀ e, T e ≠ 0) ∧ ∀ e (j : K → L.ι), (∀ k, ⊤ ≤ (u.ex (z k e)).left ⁻¹ᵁ L.U (j k)) → valAt' (pt e) (LB.wchart L φ j) (t.s j).val = T e * ∏ k, u.fr (j k) (z k e) ^ ep k := by
  first | exact @GlobalTheory.exists_entire_generator_div_frames | exact GlobalTheory.exists_entire_generator_div_frames | (intros; apply GlobalTheory.exists_entire_generator_div_frames <;> assumption)
