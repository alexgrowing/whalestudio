import Formalism.RealPlaceAnalysis.Complexify

open Matrix

noncomputable section

namespace Formalism.REAL

def lminor {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) (i : Fin (n + 1)) : ℂ :=
  (Matrix.of fun a b : Fin i => x (Fin.castLE (Nat.lt_succ_iff.mp i.isLt) a)
    (Fin.castLE (Nat.lt_succ_iff.mp i.isLt) b)).det

def LminorPos : Prop :=
  ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Yᴴ = Y → ∀ i : Fin (n + 1),
    (lminor (NormedSpace.exp Y) i).im = 0 ∧ 0 < (lminor (NormedSpace.exp Y) i).re

def DecayPhi : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (g : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ),
    StrictAnti lam →
    (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) →
    Yᴴ = Y → (∀ a b : Fin n, ε a = ε b → Y a b = 0) →
    ∏ i : Fin n, (if h : 0 < (i : ℕ) then
        ((lminor (NormedSpace.exp Y) ⟨i, by omega⟩).re) ^
          (-(lam ⟨(i : ℕ) - 1, by omega⟩ - lam i + 1))
      else 1) ≤
      Real.exp (-(g / 8) * min (hs Y) (Real.sqrt (hs Y) / Real.sqrt n))

end Formalism.REAL
