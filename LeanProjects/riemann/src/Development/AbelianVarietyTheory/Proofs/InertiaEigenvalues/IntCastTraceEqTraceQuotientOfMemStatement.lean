import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntCastTraceEqTraceQuotientOfMem
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intCast_trace_eq_trace_quotient_of_mem' : ∀ (L : Type) [Field L] [NumberField L] (l b : ℕ) [Fact l.Prime] (I Q : Ideal (𝓞 L)), I ⊔ Q = ⊤ → I * Q = Ideal.span {((l ^ b : ℕ) : 𝓞 L)} → ∀ [Algebra (ZMod (l ^ b)) (𝓞 L ⧸ I)] (x : 𝓞 L), x ∈ Q → ((Algebra.trace ℤ (𝓞 L) x : ℤ) : ZMod (l ^ b)) = Algebra.trace (ZMod (l ^ b)) (𝓞 L ⧸ I) (Ideal.Quotient.mk I x) := by
  first | exact @GlobalTheory.intCast_trace_eq_trace_quotient_of_mem | exact GlobalTheory.intCast_trace_eq_trace_quotient_of_mem | (intros; apply GlobalTheory.intCast_trace_eq_trace_quotient_of_mem <;> assumption)
