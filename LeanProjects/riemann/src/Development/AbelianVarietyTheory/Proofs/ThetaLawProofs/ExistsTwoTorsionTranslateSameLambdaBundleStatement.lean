import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsTwoTorsionTranslateSameLambdaBundle
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
theorem _root_.GlobalTheory.T.exists_twoTorsion_translate_same_lambdaBundle : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (e : P'.A ≅ P.A), IsMonHom e.hom → LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left → ∃ t : 𝟙_ (Over (Sp K)) ⟶ P.A, t ^ 2 = 1 ∧ LBIso P'.L (P.L.pull (e.hom ≫ ((toUnit P.A ≫ t) * 𝟙 P.A)).left) := by
  first | exact @GlobalTheory.SameLam.exists_two_torsion_translate | exact GlobalTheory.SameLam.exists_two_torsion_translate | (intros; apply GlobalTheory.SameLam.exists_two_torsion_translate <;> assumption)
