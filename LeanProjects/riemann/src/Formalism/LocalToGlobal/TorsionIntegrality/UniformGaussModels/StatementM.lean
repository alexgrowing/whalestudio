import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.GoodModelAll

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy)
open Formalism.L2.Th1.E (IntCurve curveL)

def GoodModelUniform : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
    ∃ (c : ℂ) (hc : c ≠ 0), ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p],
      IntCurve (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι)

def ThetaZScale : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ),
    ω₀ / 2 ∉ L.lattice →
  ∀ (κ n : Type) [Fintype κ] [Fintype n] (r : κ → ℂ_[p]) (s : κ → n → ℂ),
    MvPowerSeries.rescale (fun _ : n => ι c)
        (thetaZ p (Formalism.L2.Th1.F.scalePair L c hc) ι (c * ω₀) r (fun k i => c * s k i)) =
      thetaZ p L ι ω₀ r s

end Formalism.L2.Th1.Top
