import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeIntEmbEmbP

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] (L : LB G.left)

def IsFrRatio (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e e' : Fr x0 L x) (h : MvPowerSeries ρ S) : Prop :=
  ∀ m (Z : Scheme.{0}) (r : Z ⟶ (overAt x0 (Jet S ρ m)).left) (z : Z) (J : (Z ⟶ G.left) → L.ι), Good L z J →
    (val (e' m) r z J).val = gs r z ⊤ (toΓ _ (psJet m h)) * (val (e m) r z J).val

end GlobalTheory.RayEv
