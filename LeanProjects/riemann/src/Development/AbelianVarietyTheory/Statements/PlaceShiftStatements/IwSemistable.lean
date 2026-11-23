import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField

namespace GlobalTheory.IwLevel

def IwSemistable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ → ∀ (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p →
    D.IsSimple → ∀ (i : Fin D.a) (w : Ideal (𝓞 D.F)), IsPlaceOf b i w →
    w.map (b.t i) = IsLocalRing.maximalIdeal R →
    Nonempty (HTIwRep b N w) ∧
      ∀ M : HTIwRep b N w, IsProper M.s ∧ GlobalTheory.Et.IsStrictlySemistable ϖ M.s

end GlobalTheory.IwLevel
