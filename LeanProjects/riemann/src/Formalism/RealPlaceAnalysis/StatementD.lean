import Formalism.RealPlaceAnalysis.StatementA

open Finset

noncomputable section

namespace Formalism.REAL

def rhoS (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)

def OperatorMatrixNormSqBound : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n : ℕ) (A p t : ℝ)
    (W' : H) (x z : Fin n → H) (R : Fin n → Fin n → H →L[ℂ] H),
    0 < A → 0 ≤ p → 0 ≤ t → p ≤ ‖W'‖ →
    (∀ a, z a = ∑ b, R a b (x b)) → (∀ a b, ‖R a b‖ ≤ 2 * (n : ℝ)) →
    A / 2 * ‖W'‖ ^ 2 ≤ ∑ a, ‖z a‖ ^ 2 →
    ∑ b, ‖x b‖ ^ 2 ≤ t * p →
    p ≤ 8 * (n : ℝ) ^ 4 * t / A

def DomCas : Prop :=
  ∀ (n : ℕ) (lam mu : Fin n → ℝ) (c : Fin n → Fin n → ℝ),
    Antitone lam → Antitone mu → (∀ a b, 0 ≤ c a b) →
    lam - mu = ∑ a, ∑ b, (if a < b then c a b • root a b else 0) →
    nsq (mu + rhoS n) ≤ nsq (lam + rhoS n)

end Formalism.REAL
