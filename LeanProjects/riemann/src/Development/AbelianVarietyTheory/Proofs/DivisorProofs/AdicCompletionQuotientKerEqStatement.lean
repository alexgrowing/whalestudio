import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionQuotientKerEq
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adic_completion_quotient_ker_eq : ∀ (p : ℕ) (A : Type) [CommRing A], IsSMulRegular A (p : A) → Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) ∧ RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) = Ideal.span {(p : A)} := by
  first | exact @GlobalTheory.PadicComplQuot.quot_completion | exact GlobalTheory.PadicComplQuot.quot_completion | (intros; apply GlobalTheory.PadicComplQuot.quot_completion <;> assumption)
