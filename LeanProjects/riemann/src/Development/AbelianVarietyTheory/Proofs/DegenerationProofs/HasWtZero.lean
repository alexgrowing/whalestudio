import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

def HasWt {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G)
    (U : G.left.Opens) (f : Γ(G.left, U)) (α : X) : Prop :=
  ∀ (Z : Over S) (τ : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), g.left z ∈ U →
    gs ((τ ≫ i) * g).left z U f = (gm τ.left z ⊤ (charUnit S X α)).val * gs g.left z U f

def GenWt {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G)
    {Y : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (G.left ⟶ Y)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (α : X) : Prop :=
  ∀ (Z : Over S) (τ : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J : (Z.left ⟶ Y) → L.ι), Good L z J →
    val t ((τ ≫ i) * g).left z J = gm τ.left z ⊤ (charUnit S X α) * val t g.left z J

def Red {k : Type} [Field k] (Φ : FibPre k) {Y : Scheme.{0}} {L : LB Y} {π : Φ.E.B.left ⟶ Y} {N : ℕ}
    (c : ChartPull Φ.N₀ (npw L N) π) {K K' : Type} [Fintype K] [Fintype K'] {ψ : K → (Φ.E.B.left ⟶ Y)} {ε : K → ℤ}
    {φt : K' → (Φ.G.left ⟶ Y)} {εt : K' → ℤ} (t : LB.Gen (LB.LinComb L φt εt)) (b : LB.Sec (LB.LinComb L ψ ε))
    (φ : (Φ.H 1).Sec) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) (J : (Z ⟶ Y) → L.ι), Good L z J → ∀ l : Φ.N₀.ι,
    r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J (r ≫ Φ.D.q.left ≫ π) = c.idx l →
    gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) (φ.f l) = sval b (r ≫ Φ.D.q.left) z J * (val t r z J).val

end GlobalTheory.ZH.UFib
end
