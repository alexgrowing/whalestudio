import Mathlib

namespace GlobalTheory.MapOfRealAdd

theorem map_ofReal_add :
    (let d1 : {m n : Type} → Matrix m n ℝ → Matrix m n ℂ :=
      @(fun {m n : Type} (M : Matrix m n ℝ) ↦ Matrix.map M fun (t : ℝ) ↦ (↑t : ℂ));
    ∀ {m n : Type} (M N : Matrix m n ℝ), d1 (M + N) = d1 M + d1 N) := by
  intro d1 m n M N
  ext i j
  show ((M i j + N i j : ℝ) : ℂ) = (M i j : ℂ) + (N i j : ℂ)
  exact Complex.ofReal_add _ _

end GlobalTheory.MapOfRealAdd
