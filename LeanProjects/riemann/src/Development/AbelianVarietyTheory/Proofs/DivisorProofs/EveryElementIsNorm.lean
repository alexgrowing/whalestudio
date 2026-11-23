import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianFrobeniusLift
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_element_is_norm : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F'), ∃ γ : GL (Fin n) F, IsNorm s δ γ := by
  first | (exact @GlobalTheory.Shin.exists_isNorm) | (exact GlobalTheory.Shin.exists_isNorm) | (intros; apply GlobalTheory.Shin.exists_isNorm  <;> assumption)
