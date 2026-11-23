import Mathlib

open NumberField IsDedekindDomain

noncomputable section

namespace PI.UnipVal

variable {K : Type} [Field K] [NumberField K]

def vw (w : HeightOneSpectrum (𝓞 K)) (a : K) : ℤ :=
  FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a)

def plc (w : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ w.asIdeal)

def ramw (w : HeightOneSpectrum (𝓞 K)) : ℤ := vw w ((plc w : ℕ) : K)

def UnipVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)),
    (∀ n : ℕ, n ≠ 0 → vw w ((n : ℕ) : K) = ramw w * (padicValNat (plc w) n : ℤ)) ∧
    ∀ g₁ g₂ a : ℕ, g₁.Prime → g₂.Prime → g₁ ≠ g₂ →
      (vw w (((g₁ ^ a * g₂ ^ a : ℕ)) : K) : ℝ) = (ramw w : ℝ) * (if plc w = g₁ ∨ plc w = g₂ then (a : ℝ) else 0)

end PI.UnipVal

end
