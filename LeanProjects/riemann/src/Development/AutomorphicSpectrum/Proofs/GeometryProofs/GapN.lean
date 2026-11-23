import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.ExRefEff

def gapN {Ψ : Type} {N : ℕ} (ν : Ψ × Fin N → ℤ) : Option (Ψ × Fin N) → ℤ
  | none => 0
  | some p => ν p - if h : (p.2 : ℕ) + 1 < N then ν (p.1, ⟨p.2 + 1, h⟩) else 0

end GlobalTheory.CompanionTheory.Ar.ExRefEff
