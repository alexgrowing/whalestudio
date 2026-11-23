import Mathlib
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

noncomputable section

namespace GlobalTheory.Mem.CanonicalSurjection

open MvPolynomial

def bideterminantFunctionsOfShape (K : Type) [CommRing K] (N : ℕ) (ν : Fin N → ℕ) : Set (Matrix (Fin N) (Fin N) K → K) :=
  {g | ∃ (Kc : ℕ) (sz : Fin Kc → ℕ) (hsz : ∀ k, sz k ≤ N) (I : ∀ k, Fin (sz k) → Fin N),
    Formalism.GradedWeylDivisibility.shapeDeg sz = ν ∧ (∀ k, StrictMono (I k)) ∧
      g = fun Y => eval (fun v : Fin N × Fin N => Y v.1 v.2) (Formalism.GradedWeylDivisibility.bideterminant K sz hsz I)}

end GlobalTheory.Mem.CanonicalSurjection
