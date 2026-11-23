import Mathlib
import Formalism.LogFactorialBounds.DepthIIExponent

noncomputable section

namespace Formalism.ExtensionFiltration

def RankShare : Prop :=
  ∀ (D T a : ℕ) (ρ δ dA dB dtop : ℝ), 1 ≤ D → 2 * D ≤ T → 0 ≤ ρ → ρ < 1 →
    (a : ℝ) ≤ ((T : ℝ) + D + 4) / (1 - ρ) → 0 < δ →
    ((T - 1).choose D : ℝ) * δ ≤ dA → 0 < dB → dB ≤ dtop → dtop ≤ ((a + D).choose D : ℝ) * δ →
    (D : ℝ) * ρ + 7 * (D : ℝ) ^ 2 / T ≤ 1 →
    (1 - ((D : ℝ) * ρ + 7 * (D : ℝ) ^ 2 / T)) * dB ≤ dA

def BadCount : Prop :=
  ∀ db db1 db2 sh1 sh2 d d' H ε δ : ℝ,
    0 < H → 0 ≤ d' → d' ≤ H * d → 0 ≤ ε → ε ≤ 1 / 2 → 0 ≤ sh1 → 0 ≤ sh2 → sh1 + sh2 ≤ δ →
    db1 ≤ (1 + ε) * sh1 * d' / H → db2 ≤ (1 + ε) * sh2 * d' / H → db ≤ db1 + db2 →
    db ≤ 3 * δ * d

def FlatDefect : Prop :=
  ∀ w q' t2 tq td lrd : ℝ, 0 ≤ w → 0 ≤ q' → 0 ≤ t2 → 0 ≤ tq → 0 ≤ td → lrd = t2 + tq + td →
    |w * q' * (t2 + tq - td)| ≤ w * q' * lrd

end Formalism.ExtensionFiltration
