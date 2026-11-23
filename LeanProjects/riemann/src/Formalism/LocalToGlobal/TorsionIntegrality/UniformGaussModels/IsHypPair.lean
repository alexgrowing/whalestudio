import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.OneLetterGaussFinal
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementP
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementV

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def thetaOne (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (ε : ℂ_[l]) (ω₀ s : ℂ) :
    PowerSeries ℂ_[l] :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[l])
    (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))).subst
    (PowerSeries.C ε * lgF ℂ_[l] l)

def thetaOrth (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (ε : ℂ_[l]) (ω₀ : ℂ)
    {κ n : Type} [Fintype κ] [Fintype n] (r : κ → ℂ_[l]) (s : κ → n → ℂ) : MvPowerSeries n ℂ_[l] :=
  Formalism.L2.Th1.E.thetaProd r (fun k i => thetaOne l L ι ε ω₀ (s k i))

def IsHypPair {K : Type} [NormedField K] (σ : K →+* K) {E n : Type} [DecidableEq E] [Fintype n]
    (f f' : E → n → K) : Prop :=
  (∀ e i, ‖f e i‖ ≤ 1 ∧ σ (σ (f e i)) = f e i) ∧ (∀ e i, ‖f' e i‖ ≤ 1 ∧ σ (σ (f' e i)) = f' e i) ∧
  (∀ e e', ∑ i, σ (f e i) * f e' i = 0) ∧ (∀ e e', ∑ i, σ (f' e i) * f' e' i = 0) ∧
  (∀ e e', ∑ i, σ (f e i) * f' e' i = if e = e' then 1 else 0)

def thetaHyp (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (ε : ℂ_[l]) (ω₀ : ℂ)
    {E κ n : Type} [Fintype E] [Fintype κ] [Fintype n] (f f' : E → n → MaximalUnramifiedExtension l) (r : κ → ℂ_[l])
    (s : κ → n → ℂ) : MvPowerSeries (Bool × E) ℂ_[l] :=
  MvPowerSeries.subst
    (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[l] l) (Formalism.L2.Th1.D.expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype f f')
    (thetaOrth l L ι ε ω₀ r s)

end Formalism.L2.Th1.Top
