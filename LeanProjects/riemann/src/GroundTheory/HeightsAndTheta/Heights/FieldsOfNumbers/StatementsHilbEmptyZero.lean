import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

universe u

def HilbEmptyZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), (∀ W ∈ I.minimalPrimes, ¬ IsRelevant W) →
    ∀ᶠ m in Filter.atTop, hilbFn I m = 0

noncomputable def HilbEmptyZero.blockIdeal (k : Fin 2) : Ideal (MRing (fun _ : Fin 2 => Fin 2) ℚ) :=
  Ideal.span (Set.range fun i : Fin 2 => (X ⟨k, i⟩ : MRing (fun _ : Fin 2 => Fin 2) ℚ))

end GroundTheory.Heights₂.Heights.FieldNumbers
