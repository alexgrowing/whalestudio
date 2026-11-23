import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.LatticeFromNormOne

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW

def PairOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
    (L : Set (ι → K)),
    Module.finrank ℚ K = 2 → (∀ x, c (c x) = x) → p.Prime → SplitK c p →
      Unimod K c p L → Spans K L → ∃ x ∈ L, ∃ y ∈ L, hf c x y = 1

end PI.KLW
