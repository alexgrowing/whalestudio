import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLAssoc
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_assoc : ∀ (F : Type) [Field F] [Finite F], ∀ (a b c n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (γ : GL (Fin c) F → ℂ), IsCl α → IsCl β → IsCl γ → n = a + b + c → hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n := by
  first | (exact @GlobalTheory.Shin.HcAssoc.hc_assoc) | (exact GlobalTheory.Shin.HcAssoc.hc_assoc) | (intros; apply GlobalTheory.Shin.HcAssoc.hc_assoc <;> assumption)
