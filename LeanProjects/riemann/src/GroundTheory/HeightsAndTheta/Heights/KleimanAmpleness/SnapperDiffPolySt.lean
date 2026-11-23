import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperDiffPoly.Statement : Prop :=
  ∀ (t D : ℕ) (f : (Fin t → ℕ) → ℤ → ℚ) (μ : Fin t → ℤ),
    IsNumPolyLT t D (fun n c => f n (c + 1) - f n c) →
    (∀ j, IsNumPolyLT t D (fun n c => f (Function.update n j (n j + 1)) (c + μ j) - f n c)) →
    IsNumPolyLT t (D + 1) f

end

end GroundTheory.Heights₂.Heights.Kleiman
