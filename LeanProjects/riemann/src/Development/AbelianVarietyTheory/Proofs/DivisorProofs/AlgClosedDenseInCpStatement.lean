import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosedDenseInCp
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algClosed_dense_in_Cp : ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [IsAlgClosed E] (ι : E →+* ℂ_[p]), DenseRange ι := by
  first | exact @GlobalTheory.denseRange_of_isAlgClosed_padicComplex | exact GlobalTheory.denseRange_of_isAlgClosed_padicComplex | (intros; apply GlobalTheory.denseRange_of_isAlgClosed_padicComplex <;> assumption)
