import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmEqMapGm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFarSet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def SecCarried {X : Scheme.{0}} (L : LB X) (θ : L.Sec) (f : X ⟶ X) (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι) (hk : z ∈ L.U k) (hj : f z ∈ L.U j),
    (X.presheaf.germ (f ⁻¹ᵁ L.U j) z hj).hom ((f.app (L.U j)).hom (θ.f j)) =
      (gw w (𝟙 X) z j k).val * (X.presheaf.germ (L.U k) z hk).hom (θ.f k)

end GlobalTheory.Mum
