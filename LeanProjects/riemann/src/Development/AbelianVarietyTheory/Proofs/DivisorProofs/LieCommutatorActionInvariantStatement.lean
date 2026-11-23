import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCommutatorActionInvariant
import Mathlib
import Formalism.LocalRingCardinality.DataTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_commutator_action_invariant : ∀ {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] {R S : ℕ} (r₀ : Fin R) (s₀ : Fin S)
    (act : ι → Formalism.BasicNotions.TH.Mat R S →ₗ[ℂ] Module.End ℂ V),
    (∀ w X Y, Formalism.BasicNotions.TH.IsKC X → Formalism.BasicNotions.TH.IsKC Y → act w (X * Y - Y * X) = act w X * act w Y - act w Y * act w X) →
    (∀ w w', w ≠ w' → ∀ X Y, Formalism.BasicNotions.TH.IsKC X → Formalism.BasicNotions.TH.IsKC Y → act w X * act w' Y = act w' Y * act w X) →
    ∀ U : Submodule ℂ V, (∀ w X, Formalism.BasicNotions.TH.IsKC X → ∀ v ∈ U, act w X v ∈ U) →
    (∀ N : Submodule ℂ V, N ≤ U → (∀ w X, Formalism.BasicNotions.TH.IsKC X → ∀ v ∈ N, act w X v ∈ N) → N = ⊥ ∨ N = U) →
    ∀ (c c' : ι → ℂ) (T : Submodule ℂ V),
    (∀ v, v ∈ T ↔ v ∈ U ∧ ∀ w, act w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl r₀)) v = c w • v ∧
      act w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr s₀)) v = c' w • v) →
    (∀ v ∈ T, ∀ w, (∀ i, i ≠ r₀ → act w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl i)) v = 0) ∧
      ∀ j, j ≠ s₀ → act w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr j)) v = 0) →
    ∀ N : Submodule ℂ V, N ≤ T →
    (∀ w X, Formalism.BasicNotions.TH.IsKC X → (∀ a, X a (.inl r₀) = 0 ∧ X (.inl r₀) a = 0 ∧ X a (.inr s₀) = 0 ∧ X (.inr s₀) a = 0) →
      ∀ v ∈ N, act w X v ∈ N) →
    N = ⊥ ∨ N = T := by
  first | exact @GlobalTheory.BranchTop.top_irreducible | exact GlobalTheory.BranchTop.top_irreducible | (intros; apply GlobalTheory.BranchTop.top_irreducible <;> assumption)
