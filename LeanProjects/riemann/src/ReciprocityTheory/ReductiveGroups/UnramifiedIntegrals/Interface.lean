import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement

noncomputable section
open Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def JInt : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]), ‖ι (jInv L)‖ ≤ 1

def JUnram : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ d → ∀ ι : ℂ ≃+* ℂ_[l], ι (jInv L) ∈ MaximalUnramifiedExtension l

end ReciprocityTheory.ChartRestriction.L1
