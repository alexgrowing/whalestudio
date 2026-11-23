import Mathlib

noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k]

def IntM {m p : Type} (Z : Matrix m p k) : Prop := ∀ i j, Z i j ∈ 𝒪[k]

def Below {n d : ℕ} (t : k) (Y Y₀ : Matrix (Fin n) (Fin d) k) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) 𝒪[k], ∃ Z : Matrix (Fin n) (Fin d) k, IntM Z ∧
    Y = A.map (algebraMap 𝒪[k] k) * Y₀ + t • Z

def latt {n d : ℕ} (t : k) (Y₀ : Matrix (Fin n) (Fin d) k) : Submodule 𝒪[k] (Fin d → k) :=
  Submodule.span 𝒪[k] (Set.range Y₀ ∪ Set.range fun j : Fin d => t • (Pi.single j 1 : Fin d → k))

end PositivityTheory.Sph

end
