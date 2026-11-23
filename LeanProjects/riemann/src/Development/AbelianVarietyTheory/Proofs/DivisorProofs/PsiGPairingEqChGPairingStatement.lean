import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiGPairingEqChGPairing
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_psiG_mul_star_eq_chG : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y → ∑ᶠ x, psiG S n x * star (Y x) = ∑ᶠ x, chG S n x * star (Y x) := by
  first | (exact @GlobalTheory.psiG_pairing_eq_chG_pairing) | (exact GlobalTheory.psiG_pairing_eq_chG_pairing) | (intros; apply GlobalTheory.psiG_pairing_eq_chG_pairing <;> assumption)
