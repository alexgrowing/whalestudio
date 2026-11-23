import Mathlib

namespace GlobalTheory.SpectralLemmaThird

theorem main : (let d1 : {n : Type} → [Fintype n] → Matrix n n ℂ → (n → ℂ) → (n → ℂ) → ℂ := @(fun {n : Type} [Fintype n] (M : Matrix n n ℂ) (u v : n → ℂ) ↦ u ⬝ᵥ Matrix.mulVec M (Star.star v)); ∀ {n : Type} [inst : Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (u v v' : n → ℂ), d1 M u (v + v') = d1 M u v + d1 M u v') := by
  intro d1 n _ _ M u v v'
  simp only [d1, star_add, Matrix.mulVec_add, dotProduct_add]

end GlobalTheory.SpectralLemmaThird
