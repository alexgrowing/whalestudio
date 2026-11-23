import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendLinearIndependentDifferentials
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_linear_independent_differentials : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.FiniteType R B] (d : ℕ) (ι : Type) (x : ι → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (x i)) → ∃ (t : Fin d → B) (e : ι ↪ Fin d), (∀ i, t (e i) = x i) ∧ LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) := by
  first | exact @GlobalTheory.kaehler_baseChange_independent_extend | exact GlobalTheory.kaehler_baseChange_independent_extend | (intros; apply GlobalTheory.kaehler_baseChange_independent_extend <;> assumption)
