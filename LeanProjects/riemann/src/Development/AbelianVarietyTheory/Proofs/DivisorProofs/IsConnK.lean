import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

def IsConnK {R : Type} [CommRing R] {k : Type} [Field k] (A : Over (Sp R)) (L : LB A.left) (A₀ : Over (Sp k))
    (m₀ : A₀.left ⟶ A.left) (D' : R → k) {J : Type} (V : J → A.left.Opens) (jj : J → L.ι)
    (ed : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)) : Prop :=
  GlobalTheory.KS.LocDerK A₀.hom A.hom m₀ D' ⊤ ed ∧ ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ L.U (jj i)) ∧
    ∀ i i', ed (V i ⊓ V i') (rsT (L.g (jj i) (jj i')).val (V i ⊓ V i')) =
      pbT m₀ (L.g (jj i) (jj i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) *
        (rsT (pb i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (pb i) (m₀ ⁻¹ᵁ (V i ⊓ V i')))

end GlobalTheory.HeatConn
