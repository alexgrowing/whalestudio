import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherNormalizationFiniteAevalPowAdd
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noether_normalization_finite_aeval_pow_add : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (t a : A), (Polynomial.aeval (R := k) t).Finite → ∃ M : ℕ, (Polynomial.aeval (R := k) (t ^ M + a)).Finite := by
  first | exact @GlobalTheory.noether_trick | exact GlobalTheory.noether_trick | (intros; apply GlobalTheory.noether_trick <;> assumption)
