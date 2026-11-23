import Mathlib

namespace GlobalTheory.RealEmbeddingLemmaFirst

theorem main : (let d1 : {m n : Type} → Matrix m n ℝ → Matrix m n ℂ := @(fun {m n : Type} (M : Matrix m n ℝ) ↦ Matrix.map M fun (t : ℝ) ↦ (↑t : ℂ)); ∀ {m n k : Type} [inst : Fintype n] (M : Matrix m n ℝ) (N : Matrix n k ℝ), d1 (M * N) = d1 M * d1 N) := by
  intro d1 m n k _ M N
  exact Matrix.map_mul (f := Complex.ofRealHom)

end GlobalTheory.RealEmbeddingLemmaFirst
