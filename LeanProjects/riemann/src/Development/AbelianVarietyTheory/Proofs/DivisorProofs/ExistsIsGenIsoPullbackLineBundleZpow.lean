import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullPow

variable {X Y Z : Scheme.{0}}

theorem pull_pw_g (H : LB X) (g : Z ⟶ X) (n : ℤ) (i j : ((GlobalTheory.AbLaw.pw H n).pull g).ι) :
    ((GlobalTheory.AbLaw.pw H n).pull g).g i j = ((H.pull g).g i j) ^ n := by
  show (∏ k : PUnit, _) = (∏ k : PUnit, _) ^ n
  erw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
  erw [map_zpow, map_zpow]
  rfl

theorem div_pull_pw_g (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y) (n : ℤ)
    (p q : (LB.div ((GlobalTheory.AbLaw.pw H n).pull g) ((GlobalTheory.AbLaw.pw M n).pull f)).ι) :
    (LB.div ((GlobalTheory.AbLaw.pw H n).pull g) ((GlobalTheory.AbLaw.pw M n).pull f)).g p q =
      ((LB.div (H.pull g) (M.pull f)).g p q) ^ n := by
  simp only [LB.div, pull_pw_g]
  erw [map_zpow, map_zpow, ← inv_zpow, ← mul_zpow]
  rfl

def isoPow {M : LB X} {H : LB Y} {f : Z ⟶ X} {g : Z ⟶ Y} (w : LB.Iso (M.pull f) (H.pull g)) (n : ℤ) :
    LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g) where
  s := fun p => (w.s p) ^ n

theorem isoPow_isGen {M : LB X} {H : LB Y} {f : Z ⟶ X} {g : Z ⟶ Y} (w : LB.Iso (M.pull f) (H.pull g))
    (hw : w.IsGen) (n : ℤ) : (isoPow w n).IsGen := by
  intro p q
  rw [div_pull_pw_g]
  erw [map_zpow, map_zpow]
  erw [hw p q, mul_zpow]
  rfl

theorem exists_isGen_iso_pw : ∀ {X Y Z : Scheme.{0}} (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y)
    (w : LB.Iso (M.pull f) (H.pull g)), M.IsLB → H.IsLB → w.IsGen → ∀ n : ℤ,
    ∃ w' : LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g), w'.IsGen :=
  fun _ _ _ _ w _ _ hw n => ⟨isoPow w n, isoPow_isGen w hw n⟩

end GlobalTheory.PullPow
