import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeSubrepresentationExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
open GlobalTheory.LocFinIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_type_subrepresentation_exists : ∀ (G : Type) [Group G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (h1 : (1 : G) ∈ K) (hmul : ∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) (hst : ∀ k ∈ K, ∀ x ∈ D, ρ k x ∈ D) (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ), (∀ i, b i ∈ D) → (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) → ∃ W : Submodule (MonoidAlgebra ℂ (subK K h1 hmul)) (repD ρ D K h1 hmul hst).asModule, ∀ u, u ∈ W ↔ (((repD ρ D K h1 hmul hst).asModuleEquiv u : D) : V) ∈ Submodule.span ℂ (Set.range b) := by
  first | exact @GlobalTheory.FinSpanSub.main | exact GlobalTheory.FinSpanSub.main | (intros; apply GlobalTheory.FinSpanSub.main <;> assumption)
