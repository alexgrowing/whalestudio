import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentiallyKnown_of_same_lambdaBundle : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (y : KeyIn K) (P : Out.PolAV (Sp K)) (e : P.A ≅ y.P.A), IsMonHom e.hom → LamIs P.A P.L y.P.A (abelian₂ y.P.A y.P.L) e.hom.left → Known K y → PotKnown K P := by
  first | exact @GlobalTheory.KeyFam.SameLam.potKnown_of_lamIs | exact GlobalTheory.KeyFam.SameLam.potKnown_of_lamIs | (intros; apply GlobalTheory.KeyFam.SameLam.potKnown_of_lamIs <;> assumption)
