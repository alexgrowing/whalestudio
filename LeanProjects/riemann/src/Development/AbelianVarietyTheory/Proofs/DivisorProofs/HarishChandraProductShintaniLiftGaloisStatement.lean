import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductShintaniLiftGalois
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraProduct_shintaniLift_galois : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (θ : AlgebraicClosure F' →* ℂ) (t : F' ≃ₐ[F] F') (L : List (ℕ × ℕ)) (n : ℕ), n = deg (liftL (Nat.card F) (Module.finrank F F') L) → ∀ x : GL (Fin n) F', J θ (liftL (Nat.card F) (Module.finrank F F') L) n (galAct F F' n t x) = J θ (liftL (Nat.card F) (Module.finrank F F') L) n x := by
  first | (exact @GlobalTheory.Shin.J_liftL_galAct) | (exact GlobalTheory.Shin.J_liftL_galAct) | (intros; apply GlobalTheory.Shin.J_liftL_galAct <;> assumption)
