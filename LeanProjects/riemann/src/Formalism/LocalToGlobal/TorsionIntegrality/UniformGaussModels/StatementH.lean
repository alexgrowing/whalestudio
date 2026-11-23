import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.GoodModelAll
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementL

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

def IntOpTwoOrth : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → HasCMBy d L →
  ∀ (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W → ‖W.a₁‖ = 1 →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → omegaK d * (ω₀ / 2) ∉ L.lattice → conj (omegaK d) * (ω₀ / 2) ∉ L.lattice →
  ∀ (n : Type) [Fintype n] (κ : Type) [Fintype κ] (r : κ → ℂ_[2]) (s : κ → n → ℂ) (N : ℕ),
    (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ 2 ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    JetsIntegral (thetaZ 2 L ι ω₀ r s) ∧
    ∀ P : MvPolynomial n ℂ_[2], (∀ m, ‖MvPolynomial.coeff m P‖ ≤ 1) →
      ‖jetPair P (thetaZ 2 L ι ω₀ r s)‖ ≤ 1

def GoodModelTwo : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2],
    ∃ (c : ℂ) (hc : c ≠ 0) (W : WeierstrassCurve ℂ_[2]),
      Unif 2 (Formalism.L2.Th1.F.scalePair L c hc) ι W ∧ IntCurve W ∧ ‖W.a₁‖ = 1

end Formalism.L2.Th1.Top
