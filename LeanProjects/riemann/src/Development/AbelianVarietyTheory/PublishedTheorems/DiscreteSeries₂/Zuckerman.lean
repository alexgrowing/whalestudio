import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BranchingSupport

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def Zuckerman : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu →
    (∀ a c, a < c → 2 ≤ mu a - mu c) →
    (∀ (l : ℕ) (RI : Sub (2 * r + k + 1) l → Rep k r), (∀ I, (RI I).IsDS ε (addSet mu I.1)) →
      ∃ io pr, TensRaw (cmp l) R RI io pr) ∧
    (∀ RI : Fin (2 * r + k + 1) → Rep k r, (∀ s, (RI s).IsDS ε (mu - Pi.single s 1)) →
      ∃ io pr, TensRaw dualM R RI io pr)

end BranchingSupport
