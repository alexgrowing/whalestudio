import Formalism.LocalToGlobal.AlgebraicTheory.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.E (IntCurve curveL ptOf px py gT OneUnit)
open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.Top (thetaZ)
open Formalism.L2.Th1.G (linSub)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

def IsQInt (dK : ℕ) (α : ℂ) : Prop := ∃ m n : ℤ, α = (m : ℂ) + (n : ℂ) * omegaK dK

def UnitKerInt : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → ¬ p ∣ dK → IntCurve (curveL p L ι) →
  ∀ (α t : ℂ), IsQInt dK α → ‖ι α‖ = 1 → α * t ∈ L.lattice → t ∉ L.lattice →
    ‖px (curveL p L ι) (ptOf p L ι t)‖ ≤ 1 ∧ ‖py (curveL p L ι) (ptOf p L ι t)‖ ≤ 1

def EtPower : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → ¬ p ∣ dK → IntCurve (curveL p L ι) →
  ∀ (α t : ℂ) (M : ℕ), IsQInt dK α → ‖ι α‖ = 1 → α * t ∈ L.lattice → t ∉ L.lattice → 0 < M → (M : ℂ) * t ∈ L.lattice →
    ‖ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0)‖ = 1 ∧
    ∃ V : PowerSeries ℂ_[p], OneUnit V ∧
      gT p L ι t ^ M = PowerSeries.C (ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0) ^ M) * V

def EtJetsSigma : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → ¬ p ∣ dK → IntCurve (curveL p L ι) →
  ∀ (α t : ℂ) (M : ℕ), IsQInt dK α → ‖ι α‖ = 1 → α * t ∈ L.lattice → 0 < M → (M : ℂ) * t ∈ L.lattice →
  ∀ i : ℕ, ‖ι (iteratedDeriv i (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L)) 0)‖ * ‖(M : ℂ_[p])‖ ^ i ≤ 1

def EtJetsTh0 : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → ¬ p ∣ dK → IntCurve (curveL p L ι) →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (α t : ℂ) (M : ℕ), IsQInt dK α → ‖ι α‖ = 1 → α * t ∈ L.lattice → 0 < M → (M : ℂ) * t ∈ L.lattice →
  ∀ i : ℕ, ‖ι (iteratedDeriv i (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) 0)‖ * ‖(M : ℂ_[p])‖ ^ i ≤ 1

def EtThetaZ : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → ¬ p ∣ dK → IntCurve (curveL p L ι) →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ n : Type) [Fintype κ] [Fintype n] [DecidableEq n] (r : κ → ℂ_[p]) (s : κ → n → ℂ) (α : ℂ) (M : ℕ),
    IsQInt dK α → ‖ι α‖ = 1 → 0 < M → (∀ k, ‖r k‖ ≤ 1) →
    (∀ k i, α * s k i ∈ L.lattice) → (∀ k i, (M : ℂ) * s k i ∈ L.lattice) →
    JetsIntegral (linSub (scl n (M : ℂ_[p])) (thetaZ p L ι ω₀ r s))

end Formalism.L2.AlgTh
