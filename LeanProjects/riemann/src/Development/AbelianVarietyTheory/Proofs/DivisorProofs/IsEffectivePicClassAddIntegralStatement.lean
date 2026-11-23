import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEffectivePicClass_add_integral : ∀ {X : Scheme.{0}} [IsIntegral X] (a b : GlobalTheory.CechPic.Pic X), GlobalTheory.EffBound.Eff a → GlobalTheory.EffBound.Eff b → GlobalTheory.EffBound.Eff (a + b) := by
  first | exact @GlobalTheory.EffBound.eff_add | exact GlobalTheory.EffBound.eff_add | (intros; apply GlobalTheory.EffBound.eff_add <;> assumption)
