import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def PolyOfDiffsExact.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (h : (K → ℤ) → ℚ),
    (∀ k, ∃ q : MvPolynomial K ℚ, ∀ m : K → ℤ, h m - h (m - Pi.single k 1) = eval (fun j => (m j : ℚ)) q) →
    ∃ p : MvPolynomial K ℚ, ∀ m : K → ℤ, h m = eval (fun j => (m j : ℚ)) p

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
