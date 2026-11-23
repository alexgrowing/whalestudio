import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def VeryAmpleSnapper.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x), IsSubvar x (primeOf (S := k) x) e → IsVeryAmple Nb.toSubSystem →
    (∀ (a : ℕ) (c : ℤ), FiniteDimensional k (twistMul Nb.toSubSystem a c).secs) ∧
    ∃ (Q : MvPolynomial (Fin 2) ℚ) (c₀ : ℤ), Q.totalDegree ≤ e ∧
      (∀ (a : ℕ) (c : ℤ), c₀ ≤ c →
        (Module.finrank k (twistMul Nb.toSubSystem a c).secs : ℚ) = MvPolynomial.eval ![(a : ℚ), (c : ℚ)] Q) ∧
      ∀ᶠ a : ℕ in atTop,
        (Module.finrank k (Nb.toSubSystem.pow a).secs : ℚ) = MvPolynomial.eval ![(a : ℚ), 0] Q

end

end GroundTheory.Heights₂.Heights.Kleiman
