import Formalism.MahlerMeasure.QuotientUpperBoundsOfPowerBounds

namespace Formalism.GM

def LevelConst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a r o n z j : ℕ), 1 ≤ a → 1 ≤ r → o + n + z + 1 ≤ 8 * a →
    j ≤ o → j ≤ n →
    |((padicValRat p
        (((j.factorial ^ 2 * (o + n + r + z + 1 - 2 * j + j - 1).choose j * z.factorial *
            (o - j).factorial * (n - j).factorial : ℕ) : ℚ) /
          (((z + o).factorial * n.factorial : ℕ) : ℚ)) : ℤ) : ℝ)| ≤ 3 * lgV2 p a r

end Formalism.GM
