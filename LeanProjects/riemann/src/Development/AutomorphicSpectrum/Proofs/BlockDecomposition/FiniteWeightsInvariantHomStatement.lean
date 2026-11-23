import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteWeightsInvariantHom
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_weights_invariant_hom : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)), IsPair E1 E2 → IsDerivK σ (kF E1 E2) → ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G → (⨆ μ, wtDual E μ) = ⊤ → ∀ M : Finset (Fin n → ℤ), (∀ (ν : Fin n → ℤ) (v : V), v ≠ 0 → v ∈ hwSp E1 E2 (wtR ν) → wtDual E ν ≠ ⊥ → ν ∈ M) → ∀ t ∈ invA σ E, (∀ μ ∈ M, ∀ ξ ∈ hwOf G (wtR μ), t ξ = 0) → t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.InjG.eq_zero_of_hw | exact GlobalTheory.CompanionTheory.RealCountG.InjG.eq_zero_of_hw | (intros; apply GlobalTheory.CompanionTheory.RealCountG.InjG.eq_zero_of_hw <;> assumption)
