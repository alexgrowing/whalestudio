import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalProjectionIntegralAdic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_projection_integral_adic : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (σ : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (V : Submodule (w.adicCompletion E) (Fin n → w.adicCompletion E))
    (e : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, Valued.v (e i j) ≤ 1) → (∀ x, e *ᵥ x ∈ V) →
    (∀ x ∈ V, e *ᵥ x = x) → (∀ x ∈ V, ∀ y, ∑ k, σ (x k) * (y - e *ᵥ y) k = 0) →
    ∃ (s : ℕ) (f : Module.Basis (Fin s) (w.adicCompletion E) V),
      Valued.v (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → w.adicCompletion E) k) * (f j : Fin n → w.adicCompletion E) k).det = 1 := by
  first | exact @GlobalTheory.IdempotentUnimodular.main | exact GlobalTheory.IdempotentUnimodular.main | (intros; apply GlobalTheory.IdempotentUnimodular.main <;> assumption)
