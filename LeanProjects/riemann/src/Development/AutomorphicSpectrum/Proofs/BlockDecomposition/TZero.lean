import Mathlib

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.CoefId

variable {n : ℕ}

def mon (e : Fin n → ℤ) (z : Fin n → ℂ) : ℂ := ∏ a, z a ^ e a

def dl (n : ℕ) : Fin n → ℤ := fun j => ((n - 1 - (j : ℕ) : ℕ) : ℤ)

def prs (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

def score (T : Finset (Fin n × Fin n)) : Fin n → ℤ := fun c =>
  ((T.filter fun p => p.1 = c).card : ℤ) + (((prs n \ T).filter fun p => p.2 = c).card : ℤ)

def tZero (lev : Fin n → ℕ) : Finset (Fin n × Fin n) := (prs n).filter fun p => lev p.1 < lev p.2

end GlobalTheory.CompanionTheory.CoefId
