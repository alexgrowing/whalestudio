import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def LeadingCoeffPos.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (M Nb : LineBundle k x) (q : ℕ) (m : ℤ) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) →
    Nef M.toSubSystem → Nb.toSubSystem = twistMul M.toSubSystem q m → IsVeryAmple Nb.toSubSystem →
    ((d + 1 : ℕ) : ℤ) * b < m →
    0 < interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) -
          ((d + 1 : ℕ) : ℤ) * interNum (primeOf (S := k) x)
            (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
              (fun _ : Fin d => Nb.toSubSystem))

end

end GroundTheory.Heights₂.Heights.Kleiman
