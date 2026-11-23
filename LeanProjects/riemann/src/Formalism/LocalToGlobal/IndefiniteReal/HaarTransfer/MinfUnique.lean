import Mathlib
import Formalism.LocalRingCardinality.DataCD

namespace Formalism.IndefR.Leaf

open MeasureTheory Formalism.BasicNotions

def MinfExistsUnique : Prop :=
  ∀ (p q : ℕ) (c : ENNReal), c ≠ 0 → c ≠ ⊤ →
    ∃! m : Measure (UpqT p q), m.IsHaarMeasure ∧ OmegaDensity m c

end Formalism.IndefR.Leaf
