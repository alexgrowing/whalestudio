import Mathlib

namespace Formalism.IndefR.Eqv

open scoped ContDiff

def IterSymmR : Prop :=
  ∀ (E H : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H] (g : E → H),
    ContDiff ℝ ∞ g → ∀ (n : ℕ) (x : E) (v : Fin n → E) (σ : Equiv.Perm (Fin n)),
      iteratedFDeriv ℝ n g x (v ∘ σ) = iteratedFDeriv ℝ n g x v

end Formalism.IndefR.Eqv
