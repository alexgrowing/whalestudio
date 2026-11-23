import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyEquivOfCardHom
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_linearEquiv_of_card_hom_eq : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M] [AddCommGroup N] [Module R N] [Finite N], (∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X], Nat.card (X →ₗ[R] M) = Nat.card (X →ₗ[R] N)) → Nonempty (M ≃ₗ[R] N) := by
  first | (exact @GlobalTheory.HomCount.nonempty_equiv_of_card_hom) | (exact GlobalTheory.HomCount.nonempty_equiv_of_card_hom) | (intros; apply GlobalTheory.HomCount.nonempty_equiv_of_card_hom  <;> assumption)
