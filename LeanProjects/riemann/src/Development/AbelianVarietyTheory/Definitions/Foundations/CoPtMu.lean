import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT

noncomputable section

open Finset

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def ffMu (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a : ℤ) (s : ℕ) : K :=
  ∑ d ∈ s.divisors, if ¬ p ∣ d ∧ ¬ p ∣ (s / d) then
    ((if ((s / d : ℕ) : ℤ) ≡ a [ZMOD N] then ψ ((s / d : ℕ) : ZMod (p ^ m)) * ((s / d : ℕ) : K) ^ (k - 2) else 0) -
     (if (-((s / d : ℕ) : ℤ)) ≡ a [ZMOD N] then ψ (-((s / d : ℕ) : ZMod (p ^ m))) * (-((s / d : ℕ) : K)) ^ (k - 2) else 0))
    else 0

def eeMu (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (b : ℤ) (s : ℕ) : K :=
  ∑ d ∈ s.divisors, if ¬ p ∣ d ∧ ¬ p ∣ (s / d) then
    ((if ((s / d : ℕ) : ℤ) ≡ b [ZMOD N] then ψ⁻¹ ((d : ℕ) : ZMod (p ^ m)) else 0) -
     (if (-((s / d : ℕ) : ℤ)) ≡ b [ZMOD N] then ψ⁻¹ (-((d : ℕ) : ZMod (p ^ m))) else 0))
    else 0

def coPtMu (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a b : ℤ) : ℕ → K :=
  cmul (ffMu N p m k ψ a) (eeMu N p m ψ b)

def coPtS (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d x : ℤ) (s : ℕ) : K :=
  (c : K) ^ 2 * (d : K) ^ 2 * coPtMu N p m k ψ x 1 s
    - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * coPtMu N p m k ψ (c * x) 1 s
    - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * coPtMu N p m k ψ x d s
    + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * coPtMu N p m k ψ (c * x) d s

end GlobalTheory.KummerEisensteinGalois
