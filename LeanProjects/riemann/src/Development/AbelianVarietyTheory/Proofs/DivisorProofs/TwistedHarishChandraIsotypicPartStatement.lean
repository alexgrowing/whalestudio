import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraIsotypicPart
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedHarishChandra_isotypic_part : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → Kills α A → Kills β B → Kills (hcTw t a b α β n) (hc a b A B n) := by
  first | (exact @GlobalTheory.Shin.HcIso.kills_hcTw) | (exact GlobalTheory.Shin.HcIso.kills_hcTw) | (intros; apply GlobalTheory.Shin.HcIso.kills_hcTw <;> assumption)
