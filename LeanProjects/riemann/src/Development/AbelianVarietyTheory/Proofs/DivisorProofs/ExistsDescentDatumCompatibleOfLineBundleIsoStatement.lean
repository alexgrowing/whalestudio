import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumCompatibleOfLineBundleIso
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descentDatumCompatible_of_lineBundle_iso : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB → LBIso (L.pull (pullback.fst f f)) (L.pull (pullback.snd f f)) → ∃ φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ, DescCompat f L φ := by
  first | exact @GlobalTheory.LBDescent.descCompat_of_lbIso | exact GlobalTheory.LBDescent.descCompat_of_lbIso | (intros; apply GlobalTheory.LBDescent.descCompat_of_lbIso <;> assumption)
