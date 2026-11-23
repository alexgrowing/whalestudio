import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

open Classical in

def BlocksLeadSandwich.Statement : Prop :=
  ∀ (K L : Type) [Fintype K] [Fintype L] (n a₀ : ℕ) (f : (K → ℤ) → ℤ) (g : (K ⊕ L → ℤ) → ℤ)
    (p : MvPolynomial K ℚ) (p' : MvPolynomial (K ⊕ L) ℚ),
    p.totalDegree ≤ n → p'.totalDegree ≤ n →
    (∀ b : K → ℕ, (∀ k, a₀ ≤ b k) →
      (f (fun k => (b k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (b k : ℚ)) p) →
    (∀ b : K ⊕ L → ℕ, (∀ k, a₀ ≤ b k) →
      (g (fun k => (b k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (b k : ℚ)) p') →
    (∀ e : L → ℕ, ∃ c : ℕ, ∀ d δ : K → ℕ, (∀ k, c ≤ δ k) →
      f (fun k => (d k : ℤ)) ≤ g (Sum.elim (fun k => (d k : ℤ)) fun l => (e l : ℤ)) ∧
        g (Sum.elim (fun k => (d k : ℤ)) fun l => (e l : ℤ)) ≤ f (fun k => ((d k + δ k : ℕ) : ℤ))) →
    ∀ a : K → ℤ, (∀ k, 1 ≤ a k) →
      eventualValue (mixedDiff (fun _ : Fin n => Sum.elim a (0 : L → ℤ)) g) =
        eventualValue (mixedDiff (fun _ : Fin n => a) f)

namespace BlocksLeadSandwich

end BlocksLeadSandwich

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
