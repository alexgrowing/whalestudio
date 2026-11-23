import Formalism.FrobeniusBaseCase.Statement

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

namespace Data

variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)

def UnitEntryAll : Prop :=
  ∀ (s : ℕ), 1 ≤ s → s < D.K → ∀ (c : C), D.lev c = s → ∀ (P : Z → k),
    D.m s c = MvPowerSeries.C ((-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹) *
      ∑ d, MvPowerSeries.C (P d) * X d ^ (D.q ^ s) →
    ∀ d : Z, D.v (P d) = 0 → ¬ D.InW D.zvec

def StartEqZ : Prop :=
  (∀ (s : ℕ) (c : C), 1 ≤ s → s < D.K → D.lev c = s → D.m s c = 0) → D.start = D.zvec

def LogEq (t : C → MvPowerSeries Z k) : Prop :=
  ∀ (b : C) (A : Z →₀ ℕ) (N : ℕ), A.degree ≤ N →
    coeff A (t b + ∑ c, ∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j)) =
      coeff A (D.zvec b)

def LogIffFix : Prop := ∀ t : C → MvPowerSeries Z k, NoConst t → (D.LogEq t ↔ D.Psi t = t)

def LogUnique : Prop := ∃! t : C → MvPowerSeries Z k, NoConst t ∧ D.LogEq t

def ChainIILog : Prop := ∀ t : C → MvPowerSeries Z k, NoConst t → D.LogEq t → D.InW t

end Data

end

end Formalism.BaseCaseIdentities
