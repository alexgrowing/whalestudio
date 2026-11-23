import Mathlib

noncomputable section

namespace Formalism.NormVectorIdentities.Items

def hsLogRho (C n D j0 Λ δ h : ℝ) : ℝ :=
  Real.log Λ + C * Real.log (n * D * j0 * δ * (2 + |h| + Real.log Λ))

def hsG (D n : ℝ) : ℝ := (D + 1) * (Real.log n + 1) / 2 + 1

def hsR (T D : ℕ) : ℝ := (Nat.choose (T - 1) D : ℝ)

def hsZ (T D : ℕ) (δ d : ℝ) : ℝ := 1 - hsR T D * δ / d

def HSClaimS (C : ℝ) (T D : ℕ) (n j0 Λ β ΛD ΛT J δ h d deg : ℝ) : Prop :=
  0 ≤ hsZ T D δ d ∧ hsZ T D δ d ≤ 1 ∧
    (1 - hsZ T D δ d) * ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J
        - C * (D : ℝ) ^ 2 * Real.log (Real.exp (hsLogRho C n D j0 Λ δ h) * T)
        - ((T : ℝ) + D + 1) * Real.log β - ((T : ℝ) + (D : ℝ) ^ 2) * (hsG D n + 2))
      - hsZ T D δ d * ((T : ℝ) * Real.log (2 * Real.exp (hsLogRho C n D j0 Λ δ h) * Real.sqrt β)
        + Real.log ΛD + Real.log ΛT) ≤ deg / d

end Formalism.NormVectorIdentities.Items
