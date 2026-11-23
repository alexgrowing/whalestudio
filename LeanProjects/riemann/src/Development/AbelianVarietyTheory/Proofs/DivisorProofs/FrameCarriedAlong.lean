import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarried
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def FrameAlong {X Y : Scheme.{0}} (L : LB X) (x : Y ⟶ X) (W : Y.Opens) (τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ) : Prop :=
  ∀ (z : Y) (k k' : L.ι), z ∈ W → x z ∈ L.U k → x z ∈ L.U k' →
    gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k) (τ k) =
      gm x z (L.U k ⊓ L.U k') (L.g k k') * gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k') (τ k')

def FrameCarriedAlong {X Y : Scheme.{0}} (L : LB X) (x : Y ⟶ X) (W : Y.Opens) (τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ)
    (f : X ⟶ X) (w : LB.Iso L (L.pull f)) (h : Y ⟶ Y) : Prop :=
  ∀ (z : Y) (j k : L.ι), z ∈ W → h z ∈ W → x z ∈ L.U k → x (h z) ∈ L.U j →
    gm h z (W ⊓ x ⁻¹ᵁ L.U j) (τ j) = gw w x z j k * gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k) (τ k)

end GlobalTheory.Mum
