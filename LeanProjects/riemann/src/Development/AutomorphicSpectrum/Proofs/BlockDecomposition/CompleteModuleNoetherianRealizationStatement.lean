import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompleteModuleNoetherianRealization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_module_noetherian_realization : ∀ {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B) {N : Type} [AddCommGroup N] [Module B N] [Module.Finite B N] (T : ℕ → Submodule B N), (∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n) → (∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) → ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : Algebra B R) (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module B M) (_ : IsScalarTower B R M) (_ : Module.Finite R M) (μ : N →ₗ[B] M), I.map (algebraMap B R) ≤ Ideal.jacobson ⊥ ∧ Submodule.span R (Set.range μ) = ⊤ ∧ ∀ n e, e ∈ T n ↔ μ e ∈ (I ^ (n + 1) • ⊤ : Submodule B M) := by
  first | exact @GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower | exact GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower | (intros; apply GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower <;> assumption)
