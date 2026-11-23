import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

def SiegRel {g n L : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp R} {sc : S ⟶ Sp B}
    (f : (Fin g ⊕ Fin g → ℤ) →ₗ[ℤ] D.La) (k d : ℕ) (o : Obj b L s) (c : SiegPre g n ζ sc) : Prop :=
  ∃ (χ : o.A ⟶ c.A) (χ' : c.A ⟶ o.A), IsMonHom χ ∧ IsMonHom χ' ∧ χ ≫ χ' = (𝟙 o.A) ^ k ∧
    χ' ≫ χ = (𝟙 c.A) ^ k ∧ LBIso (c.P.pull (χ ⊗ₘ χ).left) (lbPow o.P k) ∧
    (∀ a, c.lev a = (o.eta (f a) ^ d) ≫ χ) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : D.La),
      toUnit (Over.mk x) ≫ ((o.eta y ^ (d * n)) ≫ χ) = 1 ↔ ∃ a, y = f a

end GlobalTheory.UPel.HT
