import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Matrix Module

variable {ι : Type*} [Fintype ι]

noncomputable def hermQuad (A : Matrix ι ι ℂ) (x : ι → ℂ) : ℝ := (star x ⬝ᵥ (A *ᵥ x)).re

def IsPosSubspace (A : Matrix ι ι ℂ) (W : Submodule ℂ (ι → ℂ)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → 0 < hermQuad A x

noncomputable def posIndex (A : Matrix ι ι ℂ) : ℕ :=
  sSup {r | ∃ W : Submodule ℂ (ι → ℂ), IsPosSubspace A W ∧ finrank ℂ W = r}

noncomputable def negIndex (A : Matrix ι ι ℂ) : ℕ := posIndex (-A)

noncomputable def matrixSignature (A : Matrix ι ι ℂ) : ℕ × ℕ := (posIndex A, negIndex A)

section Index

variable (A : Matrix ι ι ℂ)

end Index

section Congruence

variable [DecidableEq ι]

end Congruence

section Diagonal

variable [DecidableEq ι]

end Diagonal

section Hermitian

variable [DecidableEq ι] {A : Matrix ι ι ℂ}

end Hermitian

end GroundTheory.Heights₂.Theta
