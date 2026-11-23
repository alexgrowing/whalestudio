import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularAdicCompletion
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSMulRegular_adicCompletion : ∀ (p : ℕ) (A : Type) [CommRing A], IsSMulRegular A (p : A) → IsSMulRegular (AdicCompletion (Ideal.span {(p : A)}) A) (p : AdicCompletion (Ideal.span {(p : A)}) A) := by
  first | exact @GlobalTheory.isSMulRegular_natCast_adicCompletion | exact GlobalTheory.isSMulRegular_natCast_adicCompletion | (intros; apply GlobalTheory.isSMulRegular_natCast_adicCompletion <;> assumption)
