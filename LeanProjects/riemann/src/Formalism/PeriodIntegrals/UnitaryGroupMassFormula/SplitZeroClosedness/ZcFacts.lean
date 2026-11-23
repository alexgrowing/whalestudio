import Formalism.PeriodIntegrals.SplitZeroG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.CoeffPowMulPowEqZeroOfLt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.PowerSeriesDiagonalLinear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SubstOpsHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.CoeffOneLNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.ConstantCoeffSubstEqZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SimeqCongr

noncomputable section

open Classical

namespace PI.SZGW

def ZpSimeq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (G : ℂ_[p] → MvPowerSeries σ ℂ_[p]),
    PI.BeDiagZp.ContPf.CC G → (∀ n : ℕ, PI.BeDiagZp.Simeq (G (n : ℂ_[p])) 0) →
    ∀ c : ℤ_[p], PI.BeDiagZp.Simeq (G (PI.BeDiagZp.zc c)) 0

def ZpInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (G : ℂ_[p] → MvPowerSeries σ ℂ_[p]),
    PI.BeDiagZp.ContPf.CC G → (∀ n : ℕ, PI.BeDiagZp.IntegralMv (G (n : ℂ_[p]))) →
    ∀ c : ℤ_[p], PI.BeDiagZp.IntegralMv (G (PI.BeDiagZp.zc c))

def ZcFacts : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    (∀ a b : ℤ_[p], PI.BeDiagZp.zc (a * b) = PI.BeDiagZp.zc a * PI.BeDiagZp.zc b) ∧
    (∀ a b : ℤ_[p], PI.BeDiagZp.zc (a - b) = PI.BeDiagZp.zc a - PI.BeDiagZp.zc b) ∧
    PI.BeDiagZp.zc (1 : ℤ_[p]) = 1 ∧ PI.BeDiagZp.zc (-1 : ℤ_[p]) = -1 ∧ PI.BeDiagZp.zc (2 : ℤ_[p]) = 2 ∧
    IsUnit (2 : ℤ_[p])

end PI.SZGW
