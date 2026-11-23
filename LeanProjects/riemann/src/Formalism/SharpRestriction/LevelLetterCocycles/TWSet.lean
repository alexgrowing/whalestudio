import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace Formalism.MainNotions.NAdm

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}

def TWSet (tw : NTw R H what₂ LL0 N) (i : tw.Tw) (Q : Finset (PlE H)) : Prop :=
  ∀ v ∈ Q, IsSplitPl H v ∧ v ∉ placesOver H.E (tw.l i)

def AdmQ (tw : NTw R H what₂ LL0 N) (i : tw.Tw) (Q : Finset (PlE H)) (M : ℕ) : Prop :=
  TWSet tw i Q ∧ ∀ P ∈ Q, (∃ P' ∈ Q, IsConjPl H P P') ∧
    ∃ χ : G H.E N.Om →* Multiplicative (ZMod (tw.l i ^ M)),
      IsOpen (χ.ker : Set (G H.E N.Om)) ∧ AntiHom tw.cc χ ∧
      (∀ v ∈ placesOver H.E (tw.l i), ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
        ∀ σ ∈ Dec (F := H.E) A, χ σ = 1) ∧
      (∀ v : PlE H, v ≠ P → ¬ IsConjPl H P v → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
        ∀ σ ∈ Ine (F := H.E) A, χ σ = 1) ∧
      ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := H.E) A => Multiplicative.toAdd (χ σ)

end Formalism.MainNotions.NAdm
