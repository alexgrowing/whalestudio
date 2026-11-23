import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanDecompositionLieAlgebra
import Mathlib
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_add_blockTriangular : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ), Antitone h → (∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤) → (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) → (∀ Y ∈ 𝔤, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y = Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag) → ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧ B.BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper | exact GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper | (intros; apply GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper <;> assumption)
