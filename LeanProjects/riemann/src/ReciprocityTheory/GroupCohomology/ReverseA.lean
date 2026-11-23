import Mathlib

namespace ReciprocityTheory.Coh.RevCh

open Finsupp

noncomputable section

abbrev Ch (m : ℕ) (S : Type*) := (Fin (m + 1) → S) →₀ ℤ

variable {S T U : Type*}

def bd (m : ℕ) : Ch (m + 1) S →ₗ[ℤ] Ch m S :=
  linearCombination ℤ fun t => ∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • single (t ∘ i.succAbove) (1 : ℤ)

def mp (f : S → T) (m : ℕ) : Ch m S →ₗ[ℤ] Ch m T := lmapDomain ℤ ℤ fun t => f ∘ t

def eps (m : ℕ) : ℤ := (-1) ^ (m * (m + 1) / 2)

def rv (m : ℕ) : Ch m S →ₗ[ℤ] Ch m S := eps m • lmapDomain ℤ ℤ fun t : Fin (m + 1) → S => t ∘ Fin.rev

def cone (v : S) (m : ℕ) : Ch m S →ₗ[ℤ] Ch (m + 1) S :=
  lmapDomain ℤ ℤ fun t : Fin (m + 1) → S => (Fin.cons v t : Fin (m + 2) → S)

def HHof (k : ℕ) (w : Ch (k + 1) (Fin (k + 1))) : Ch k S →ₗ[ℤ] Ch (k + 1) S :=
  linearCombination ℤ fun t => mp t (k + 1) w

def uu : (k : ℕ) → Ch (k + 1) (Fin (k + 1))
  | 0 => 0
  | k + 1 => cone (0 : Fin (k + 2)) (k + 1)
      (rv (k + 1) (single (id : Fin (k + 2) → Fin (k + 2)) 1) - single id 1 -
        HHof k (uu k) (bd k (single (id : Fin (k + 2) → Fin (k + 2)) 1)))

abbrev HH (k : ℕ) : Ch k S →ₗ[ℤ] Ch (k + 1) S := HHof k (uu k)

def Q (k : ℕ) : Prop :=
  bd (k + 1) (uu (k + 1)) + HH k (bd k (single (id : Fin (k + 2) → Fin (k + 2)) 1)) =
    rv (k + 1) (single (id : Fin (k + 2) → Fin (k + 2)) 1) - single id 1

end

end ReciprocityTheory.Coh.RevCh
