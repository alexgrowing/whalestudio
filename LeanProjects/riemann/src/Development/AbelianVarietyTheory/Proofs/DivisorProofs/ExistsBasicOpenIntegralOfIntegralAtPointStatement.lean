import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenIntegralOfIntegralAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_integral_of_integral_at_point : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (ζ : X), IntAt L α s ζ → ∀ (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ζ ∈ W → ∃ c : Γ(X, W), ζ ∈ X.basicOpen c ∧ (α.app (X.basicOpen c)).hom.IsIntegralElem ((Y.presheaf.map (homOfLE (α.preimage_mono (X.basicOpen_le c))).op).hom (chartVal L α s j W hW)) := by
  first | exact @GlobalTheory.Mum.intAt_chart | exact GlobalTheory.Mum.intAt_chart | (intros; apply GlobalTheory.Mum.intAt_chart <;> assumption)
