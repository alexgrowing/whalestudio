import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

def mulφB (D : DegPre R) (m : ℕ) (χ : D.X) : Fin 4 ⊕ Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  Sum.elim (D.famφB (m • χ)) (fun i => (mulA D.P.A m).left ≫ D.famφB χ i)

def mulεB (k k' : ℕ) : Fin 4 ⊕ Fin 4 → ℤ :=
  Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i)

def MulSecB (D : DegPre R) (m : ℕ) {k k' : ℕ} (χ : D.X) (b : D.SecB k χ) (b' : D.SecB k' (m • χ)) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (mulφB D m χ) (mulεB k k')), u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (eSec D.P.A)) (GeneratorPullback.powGen D.P.L _ _ D.rig (k' - k)) ∧
    GeneratorPullback.SecRel D.P.L (D.famφB (m • χ)) (DegPre.famε k') b' (D.famφB χ) (DegPre.famε k) b (mulA D.P.A m).left
      (mulφB D m χ) (mulεB k k') u

def MulFam {I : Ideal R} {D : DegPre R} (m : ℕ) {k k' : ℕ} (F : IntFam I D k) (G : IntFam I D k') : Prop :=
  (∀ χ, MulSecB D m χ (F.f χ) (G.f (m • χ))) ∧ ∀ β : D.X, (∀ χ, β ≠ m • χ) → ∀ j, (G.f β).f j = 0

end

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

def MulSecK (C : LabCover D) (m : ℕ) {k k' : ℕ} (θ : SecK C.P.L.L C.α k) (S : SecK C.P.L.L C.α k') : Prop :=
  ∃ u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![(k' : ℤ), -(k : ℤ)]), u.IsGen ∧
    ∀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J, Good C.P.L.L z J →
      sval S p z J = (val u (p ≫ C.α) z J).val * sval θ (p ≫ (mulA C.A.A m).left) z J

end GlobalTheory.Mum
