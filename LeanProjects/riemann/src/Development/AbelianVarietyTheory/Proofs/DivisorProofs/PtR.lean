import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThFam

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev ptR (χ : D.X) : Spec (CommRingCat.of R) ⟶ D.P.A.left :=
  (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ D.c χ).left

def unitAt {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) :
    (FractionRing R)ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map ((Z.presheaf.germ ⊤ z trivial).hom.comp
    (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)).toMonoidHom

def Reads (κ : D.X → (FractionRing R)ˣ) : Prop :=
  ∃ g : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptR D χ) (fun _ => -1)),
    (∀ χ, (g χ).IsGen) ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
      (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (D.psi χ) r z J = unitAt r z (κ χ) * val (g χ) (r ≫ jK R) z J

def lead {X : Type} [AddCommGroup X] (κ : X → (FractionRing R)ˣ) (k : ℕ) (α mu : X) : (FractionRing R)ˣ :=
  κ mu ^ k * (κ (mu + α) * (κ mu)⁻¹ * (κ α)⁻¹)

end GlobalTheory.ThFam
