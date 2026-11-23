import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfCompEq

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

def chartVal {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) {k : ℕ} (s : SecK L α k) (j : L.ι) (W : X.Opens)
    (hW : W ≤ L.U j) : Γ(Y, α ⁻¹ᵁ W) :=
  (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op).hom (s.f (fun _ => j))

def IntAt {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) {k : ℕ} (s : SecK L α k) (x : X) : Prop :=
  ∃ (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), x ∈ W ∧ IsAffineOpen W ∧
    (α.app W).hom.IsIntegralElem (chartVal L α s j W hW)

end GlobalTheory.Mum
