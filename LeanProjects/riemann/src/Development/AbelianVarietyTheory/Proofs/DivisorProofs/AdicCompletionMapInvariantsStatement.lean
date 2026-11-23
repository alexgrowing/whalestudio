import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionMapInvariants
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_map_injective_and_invariants : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → (M →ₗ[A] M)),
    Function.Injective f → (∀ x, x ∈ LinearMap.range f ↔ ∀ σ, g σ x = x) →
    Function.Injective (AdicCompletion.map J f) ∧
      ∀ y, y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ σ, AdicCompletion.map J (g σ) y = y := by
  first | exact @GlobalTheory.adicCompletion_map_invariants | exact GlobalTheory.adicCompletion_map_invariants | (intros; apply GlobalTheory.adicCompletion_map_invariants <;> assumption)
