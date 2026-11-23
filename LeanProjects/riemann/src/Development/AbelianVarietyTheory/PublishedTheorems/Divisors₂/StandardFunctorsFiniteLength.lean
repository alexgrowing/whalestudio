import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.Published

def StandardFunctorsFiniteLength : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ) (d : Fin r → ℕ),
    (∀ a, 0 < d a) →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (∑ a, d a)) k) V),
      IsSmooth π → HasFiniteLength π → HasFiniteLength (jac (m := fun a => Fin (d a)) finSigmaFinEquiv π)) ∧
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W),
      IsSmooth ρ → HasFiniteLength ρ → HasFiniteLength (parInd (m := fun a => Fin (d a)) finSigmaFinEquiv ρ)

end GlobalTheory.Published

end
