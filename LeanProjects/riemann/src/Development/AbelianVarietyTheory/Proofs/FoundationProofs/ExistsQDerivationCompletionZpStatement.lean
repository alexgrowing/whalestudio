import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQDerivationCompletionZp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_qDerivation_completion_Zp : ∀ (p : ℕ) [Fact p.Prime], ∃ D : Derivation ℤ (O0 p) (O0 p), D (qO p) = qO p ∧
    ∀ r : ℤ_[p], D (algebraMap ℤ_[p] (O0 p) r) = 0 := by
  first | exact @GlobalTheory.K5.QDer.exists_qDer | exact GlobalTheory.K5.QDer.exists_qDer | (intros; apply GlobalTheory.K5.QDer.exists_qDer <;> assumption)
