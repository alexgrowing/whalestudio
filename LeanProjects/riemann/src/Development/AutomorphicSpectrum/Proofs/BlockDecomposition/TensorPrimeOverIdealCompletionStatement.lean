import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPrimeOverIdealCompletion
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_prime_over_ideal_completion : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] [Module.Finite R M] [IsNoetherianRing (R ⊗[B] C)] (I : Ideal B) (y : M), (∀ n : ℕ, y ⊗ₜ[B] (1 : C) ∈ LinearMap.range ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C)) → ∀ Q₁ : Ideal (R ⊗[B] C), Q₁.IsPrime → I.map (algebraMap B R) ≤ Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) → ∃ w : R ⊗[B] C, w ∉ Q₁ ∧ w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change | exact GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change | (intros; apply GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change <;> assumption)
