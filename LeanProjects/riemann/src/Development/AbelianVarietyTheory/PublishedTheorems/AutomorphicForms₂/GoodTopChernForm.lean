import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

noncomputable section

namespace GlobalTheory.Published

open AlgebraicGeometry CategoryTheory MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

def GoodTopChernForm : Prop :=
  ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (m : ℕ) (E : Fr (ratOf X) (fun _ : Unit => m) 0)
    (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ),
    IsMetricOn E O H → IsGood E O H → IsMetricOn E ⊤ H₀ →
      ∀ t : ℝ, HasChernIntegral E ⊤ H₀ (MvPolynomial.X ((), X.dim)) t →
        HasChernIntegral E O H (MvPolynomial.X ((), X.dim)) t

end GlobalTheory.Published

end
