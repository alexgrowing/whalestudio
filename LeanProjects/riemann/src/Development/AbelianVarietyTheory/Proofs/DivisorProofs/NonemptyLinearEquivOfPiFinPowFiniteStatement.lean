import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_linearEquiv_of_pi_fin_pow_finite : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M] [AddCommGroup N] [Module R N] [Finite N] (l : ℕ), 0 < l → Nonempty ((Fin l → M) ≃ₗ[R] (Fin l → N)) → Nonempty (M ≃ₗ[R] N) := by
  first | (exact @GlobalTheory.PowCancel.cancel_pow) | (exact GlobalTheory.PowCancel.cancel_pow) | (intros; apply GlobalTheory.PowCancel.cancel_pow  <;> assumption)
