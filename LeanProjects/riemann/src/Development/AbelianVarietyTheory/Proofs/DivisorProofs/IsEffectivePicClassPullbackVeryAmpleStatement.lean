import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassPullbackVeryAmple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEffectivePicClass_pullback_veryAmple : ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (hH : H.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∀ (φ : Y ⟶ X), Nonempty Y → GlobalTheory.EffBound.Eff (GlobalTheory.CechPic.pull φ (GlobalTheory.CechPic.cls H hH)) := by
  first | exact @GlobalTheory.EffBound.eff_pull_of_veryAmpleBy | exact GlobalTheory.EffBound.eff_pull_of_veryAmpleBy | (intros; apply GlobalTheory.EffBound.eff_pull_of_veryAmpleBy <;> assumption)
