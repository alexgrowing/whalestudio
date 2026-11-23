import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
theorem _root_.GlobalTheory.T.eq_of_framedPoint_lies_over_torus_extension : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre F) (w w' : Frm D.toPre F 1 g.b) (x x' : TFK (R := R) F ⟶ A.A) (fr : FrAt x) (fr' : FrAt x'), w.IsGen → w'.IsGen → fr.IsGen → fr'.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g w' x' fr' → x = x' := by
  first | exact @GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver | exact GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver | (intros; apply GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver <;> assumption)
