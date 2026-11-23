import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetMulVectorType
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliDet_mul_vectorType : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (x : Fin (m + 1) → A), GlRel E → (∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0) → ∀ (u : ℂ) (j : Fin (m + 1)), qdet E u * x j = x j * qdet E u + ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) • (x a * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) := by
  first | exact @GlobalTheory.qdet_mul_vector | exact GlobalTheory.qdet_mul_vector | (intros; apply GlobalTheory.qdet_mul_vector <;> assumption)
