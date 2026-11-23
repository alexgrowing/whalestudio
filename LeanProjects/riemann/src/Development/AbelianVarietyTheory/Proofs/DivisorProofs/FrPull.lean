import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.BaseTerms

def FrPull {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    {A : PolAV (Sp (FractionRing V))} {A₂ : PolAV (Sp (FractionRing V'))} {ψ : A₂.A.left ⟶ A.A.left}
    (w : LB.Iso A₂.L (A.L.pull ψ)) (f : FractionRing V →+* FractionRing V')
    (x₂ : TFK (R := V') (FractionRing V') ⟶ A₂.A) (fr₂ : FrAt x₂) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x)
    (ρ : FractionRing V') : Prop :=
  ∀ (z : (TFK (R := V') (FractionRing V')).left) (J : ((TFK (R := V') (FractionRing V')).left ⟶ A.A.left) → A.L.ι)
    (J' : ((TFK (R := V') (FractionRing V')).left ⟶ A₂.A.left) → A₂.L.ι), Good A.L z J → Good A₂.L z J' →
    ((gw w x₂.left z (J (x₂.left ≫ ψ)) (J' x₂.left) : _) * (val fr₂ (𝟙 _) z J' : _) : ((TFK (R := V') (FractionRing V')).left.presheaf.stalk z)) =
      @id ((TFK (R := V') (FractionRing V')).left.presheaf.stalk z) (GlobalTheory.UT.cst (R := V') (FractionRing V') z ρ) *
        (val fr (show (TFK (R := V') (FractionRing V')).left ⟶ (TFK (R := V) (FractionRing V)).left from spMap f) z J : _)

end GlobalTheory.Poinc.Sep.BaseTerms
