import Mathlib
import Formalism.PeriodIntegrals.BeConjNorm
import Formalism.PeriodIntegrals.PhNormUnits
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsOfCalculation

noncomputable section

open Classical

namespace PI.BeConjNormW

open PI.PhNormUnits

def IntInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f g : PowerSeries ℂ_[p]), PowerSeries.constantCoeff f = 0 →
    PowerSeries.constantCoeff g = 0 → ‖PowerSeries.coeff 1 f‖ = 1 → (∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) →
    PowerSeries.subst f g = PowerSeries.X → ∀ n, ‖PowerSeries.coeff n g‖ ≤ 1

def LinCoeff : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex : PowerSeries ℂ_[p]), PowerSeries.constantCoeff ex = 0 →
    PowerSeries.subst ex l = PowerSeries.X → ∀ c : ℂ_[p],
    PowerSeries.coeff 1 (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]) = c

def StepCore : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), PowerSeries.constantCoeff l = 0 → PowerSeries.constantCoeff ex = 0 →
    PowerSeries.subst ex l = PowerSeries.X → PowerSeries.constantCoeff ph = 0 →
    ∀ (S : Set (ℂ_[p] × ℂ_[p])),
    (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) →
    (∀ α ∈ S, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 * α.2 = zc n) →
    (∀ α ∈ S, ∃ β ∈ S, ∃ γ ∈ S, ‖β.1‖ = 1 ∧ ‖γ.1‖ = 1 ∧ α = β + γ) →
    (∀ α ∈ S, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))) →
    Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)) →
    ∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1)))

theorem beConjNorm_of (h : StepCore) : PI.BeConjNorm.BeConjNorm := h

end PI.BeConjNormW
