import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.GoodModelAll
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IsotropicVanish

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer)
open Formalism.G (unitBall)

def pairsK (dK p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Set.range fun mn : ℤ × ℤ =>
    (ι ((mn.1 : ℂ) + (mn.2 : ℂ) * omegaK dK), ι ((mn.1 : ℂ) + (mn.2 : ℂ) * (1 - omegaK dK))))

def CalcP : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
    Formalism.L2.Th1.C.Frame (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) ∧
    Formalism.L2.Th1.C.F1 (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) ∧
    (∀ a b : ℂ_[p], (a, b) ∈ pairsK dK p ι →
      Formalism.L2.Th1.C.EndInt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) a ∧
      Formalism.L2.Th1.C.PhNormAt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) a b ∧
      Formalism.L2.Th1.C.AdjAt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) a b) ∧
    (∀ a : ℂ_[p], (a, a) ∈ pairsK dK p ι → Formalism.L2.Th1.C.IsBinomScalar (unitBall ℂ_[p]) a)

end Formalism.L2.Th1.Top
