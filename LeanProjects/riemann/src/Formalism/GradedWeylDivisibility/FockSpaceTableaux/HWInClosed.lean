import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem hwInClosed_of (h1 : HWLine) (h2 : RowDivClosedGraded) : HWInClosed := by
  intro r n hn ν hν M hMle hM hne
  obtain ⟨v, hvM, hv0, hkill⟩ := lhwin_exists_killed h2 M hM hne
  obtain ⟨c, hc⟩ := h1 ℚ r n hn ν hν v (hMle hvM) hkill
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv0 (by simpa using hc)
  have e : hw ℚ hn ν = c⁻¹ • v := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e]
  exact M.smul_mem _ hvM

end Formalism.GradedWeylDivisibility
