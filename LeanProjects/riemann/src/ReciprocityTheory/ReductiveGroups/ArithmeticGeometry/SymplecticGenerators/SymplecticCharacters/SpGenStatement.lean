import Mathlib

open Matrix

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

def spTransl {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  fromBlocks 1 S 0 1

def spDiag {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  fromBlocks (U : Matrix (Fin g) (Fin g) ℤ) 0 0 ((↑U⁻¹ : Matrix (Fin g) (Fin g) ℤ)ᵀ)

def spGens (g : ℕ) : Set (Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :=
  {M | ∃ S : Matrix (Fin g) (Fin g) ℤ, S.IsSymm ∧ M = spTransl S} ∪
    {M | ∃ U : (Matrix (Fin g) (Fin g) ℤ)ˣ, M = spDiag U} ∪ {J (Fin g) ℤ}

def SpGenStatement : Prop :=
  ∀ g : ℕ, ∀ M ∈ symplecticGroup (Fin g) ℤ, M ∈ Submonoid.closure (spGens g)

end ReciprocityTheory.ChartRestriction.G.Key.Chi
