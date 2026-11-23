import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalExpProductDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_exp_product_decomposition : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ 𝔤 𝔨 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) → (∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤) → 𝔨 ≤ 𝔤 → 𝔟 ≤ 𝔤 → 𝔤 ≤ 𝔨 ⊔ 𝔟 → ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  first | exact @GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed | exact GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed | (intros; apply GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed <;> assumption)
