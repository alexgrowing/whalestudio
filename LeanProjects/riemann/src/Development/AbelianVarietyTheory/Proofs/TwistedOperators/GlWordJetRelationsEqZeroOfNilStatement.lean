import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlWordJetRelationsEqZeroOfNil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glWordJetRelations_eq_zero_of_nil : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), LowData ε E (LamOf ε lam) u j → (∀ a b : Fin n, a < b → ε a ≠ ε b → 2 * (n : ℝ) + 1 ≤ lam a - lam b) → JetRel ε E (LamOf ε lam) u j B → B [] = 0 → ∀ l, B l = 0 := by
  first | exact @GlobalTheory.SphJet.jetRel_eq_zero_of_nil | exact GlobalTheory.SphJet.jetRel_eq_zero_of_nil | (intros; apply GlobalTheory.SphJet.jetRel_eq_zero_of_nil <;> assumption)
