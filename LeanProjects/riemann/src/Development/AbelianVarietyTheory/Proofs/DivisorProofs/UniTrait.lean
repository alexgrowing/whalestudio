import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def GeomIso {K₀ K' Ω : Type} [CommRing K₀] [CommRing K'] [CommRing Ω] (A₀ : PolAV (Sp K₀)) (A' : PolAV (Sp K'))
    (e₀ : K₀ →+* Ω) (e' : K' →+* Ω) : Prop :=
  ∃ (B : PolAV (Sp Ω)) (b₀ : B.A.left ⟶ A₀.A.left) (b' : B.A.left ⟶ A'.A.left),
    IsGrpPullback B.A A₀.A (spMap e₀) b₀ ∧ LBIso B.L (A₀.L.pull b₀) ∧
    IsGrpPullback B.A A'.A (spMap e') b' ∧ LBIso B.L (A'.L.pull b')

def UniTrait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (G' : Over (Sp W)) (_ : GrpObj G')
    (_ : IsCommMonObj G') (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
    (_ : Unif (maximalIdeal W) D' A' G') (_ : IsPullDeg φ D D'.toPre) (a : A'.A.left ⟶ A.A.left),
    GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsSemiAbelian G' ∧ IsFib φ A A' a

end GlobalTheory.Mum
