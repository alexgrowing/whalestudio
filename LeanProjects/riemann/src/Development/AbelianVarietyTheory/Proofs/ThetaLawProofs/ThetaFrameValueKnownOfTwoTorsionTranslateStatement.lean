import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfTwoTorsionTranslate
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
theorem _root_.GlobalTheory.T.thetaFrameValueKnown_of_twoTorsion_translate : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] (y y' : KeyIn K) (e : y'.P.A ≅ y.P.A) (t : 𝟙_ (Over (Sp K)) ⟶ y.P.A), IsMonHom e.hom → t ^ 2 = 1 → LBIso y'.P.L (y.P.L.pull (e.hom ≫ ((toUnit y.P.A ≫ t) * 𝟙 y.P.A)).left) → Known K y → Known K y' := by
  first | exact @GlobalTheory.KnownTwist.known_of_translate | exact GlobalTheory.KnownTwist.known_of_translate | (intros; apply GlobalTheory.KnownTwist.known_of_translate <;> assumption)
