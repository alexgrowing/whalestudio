import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def VeryAmpleHilbert.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x), IsSubvar x (primeOf (S := k) x) e → IsVeryAmple Nb.toSubSystem →
    (∀ n : ℕ, FiniteDimensional k (Nb.toSubSystem.pow n).secs) ∧
    ∃ P : Polynomial ℚ, P.natDegree ≤ e ∧
      P.coeff e * (e.factorial : ℚ) =
        (interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) : ℚ) ∧
      ∀ᶠ n : ℕ in atTop, (Module.finrank k (Nb.toSubSystem.pow n).secs : ℚ) = P.eval (n : ℚ)

end

end GroundTheory.Heights₂.Heights.Kleiman
