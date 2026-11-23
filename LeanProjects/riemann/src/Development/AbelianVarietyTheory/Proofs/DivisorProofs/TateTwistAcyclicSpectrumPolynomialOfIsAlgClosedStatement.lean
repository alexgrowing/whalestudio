import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistAcyclicSpectrumPolynomialOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistAcyclic_spectrum_polynomial_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K], IsUnit (q : K) → Acyc q (sp (Polynomial K)) := by
  first | (exact @GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed) | (exact GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed) | (intros; apply GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed  <;> assumption)
