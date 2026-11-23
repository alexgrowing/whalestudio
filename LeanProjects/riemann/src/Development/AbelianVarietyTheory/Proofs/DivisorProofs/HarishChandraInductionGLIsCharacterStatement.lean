import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLIsCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_isCharacter : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsChar ℂ ℂ α → IsChar ℂ ℂ β → IsChar ℂ ℂ (hc a b α β n) := by
  first | (exact @GlobalTheory.Shin.HCChar.hc_isChar) | (exact GlobalTheory.Shin.HCChar.hc_isChar) | (intros; apply GlobalTheory.Shin.HCChar.hc_isChar  <;> assumption)
