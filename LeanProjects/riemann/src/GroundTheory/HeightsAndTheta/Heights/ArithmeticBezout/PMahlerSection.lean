import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem MahlerSection.proof (h₁ : MahlerSectionOfConst.Statement) (h₂ : DefectConstZero.Statement)
    (h₃ : DefectConstStep.Statement) : MahlerSection.Statement := by
  have hdim : ∀ e, MahlerSectionDim e := by
    intro e
    induction e with
    | zero => exact h₁ 0 h₂
    | succ e ih => exact h₁ (e + 1) (h₃ e ih)
  intro n e δ h Z f u hprime hchow hhom hadm
  exact hdim e n δ h Z f u ⟨hprime, hchow, hhom⟩ hadm

end GroundTheory.Heights₂.Heights
