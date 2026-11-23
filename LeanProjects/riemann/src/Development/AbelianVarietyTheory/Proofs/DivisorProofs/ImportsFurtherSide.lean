import Mathlib

namespace GlobalTheory.SpectralLemmaFourth

theorem main : (let d1 : {n : Type} → [Fintype n] → Matrix n n ℂ → (n → ℂ) → (n → ℂ) → ℂ := @(fun {n : Type} [Fintype n] (M : Matrix n n ℂ) (u v : n → ℂ) ↦ u ⬝ᵥ Matrix.mulVec M (Star.star v)); ∀ {n : Type} [inst : Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (u v v' : n → ℂ), d1 M u (v - v') = d1 M u v - d1 M u v') := by
  intro d1 n _ _ M u v v'
  show u ⬝ᵥ Matrix.mulVec M (star (v - v')) = u ⬝ᵥ Matrix.mulVec M (star v) - u ⬝ᵥ Matrix.mulVec M (star v')
  rw [star_sub, Matrix.mulVec_sub, dotProduct_sub]

end GlobalTheory.SpectralLemmaFourth
