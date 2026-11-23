import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantExtending
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_extending : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)), IsPair E1 E2 → IsDerivK σ (kF E1 E2) → ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G → ∀ (M : Finset (Fin n → ℤ)) (f : ∀ μ : Fin n → ℤ, hwOf G (wtR μ) →ₗ[ℂ] hwSp E1 E2 (wtR μ)), ∃ t ∈ invA σ E, ∀ μ ∈ M, ∀ ξ : hwOf G (wtR μ), t ξ = f μ ξ := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.ExtMulti.exists_inv_multi | exact GlobalTheory.CompanionTheory.RealCountG.ExtMulti.exists_inv_multi | (intros; apply GlobalTheory.CompanionTheory.RealCountG.ExtMulti.exists_inv_multi <;> assumption)
