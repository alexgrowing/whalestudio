import Mathlib

namespace Formalism.SA.D2

def HeightMin : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (a : ι → ℝ) (κ : ℝ), 0 ≤ κ → (∀ v, 0 ≤ a v) →
    κ ^ (2 * Fintype.card ι) ≤ ∏ v, a v ^ 2 →
    (Fintype.card ι : ℝ) * κ ^ 2 ≤ ∑ v, a v ^ 2

end Formalism.SA.D2
