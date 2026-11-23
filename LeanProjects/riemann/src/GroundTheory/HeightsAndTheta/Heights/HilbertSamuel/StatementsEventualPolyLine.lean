import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def EventualPolyLine.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (D : ℕ) (f : (K → ℤ) → ℤ) (p : MvPolynomial K ℚ) (a₀ : ℕ)
    (a m : K → ℤ),
    p.totalDegree ≤ D →
    (∀ b : K → ℕ, (∀ k, a₀ ≤ b k) →
      (f (fun k => (b k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (b k : ℚ)) p) →
    ∃ r : Polynomial ℝ, r.natDegree ≤ D ∧
      r.coeff D = (eventualValue (mixedDiff (fun _ : Fin D => a) f) : ℝ) / (D.factorial : ℝ) ∧
      ∀ n : ℕ, ((MvPolynomial.eval (fun k => ((((n : ℤ) • a + m) k : ℤ) : ℚ)) p : ℚ) : ℝ) = r.eval (n : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
