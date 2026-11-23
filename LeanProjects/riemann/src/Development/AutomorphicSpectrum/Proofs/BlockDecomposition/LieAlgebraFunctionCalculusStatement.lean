import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraFunctionCalculus
import Mathlib
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_function_calculus : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ), Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) → ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by
  first | exact @GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | exact GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | (intros; apply GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise <;> assumption)
