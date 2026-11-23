import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDeltaC

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def EpDualCof : Prop :=
  ∀ D : Formalism.BasicNotions.D7, ∀ᶠ p in Filter.cofinite, ∀ z : (D.s.atP p).Ep,
    (∀ y ∈ (D.s.atP p).O, Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep (z * y) ∈ 𝒪[(D.s.atP p).Fp]) →
      z ∈ (D.s.atP p).O

def FpUnifCof : Prop :=
  ∀ D : Formalism.BasicNotions.D7, ∀ᶠ p in Filter.cofinite, ∀ x : (D.s.atP p).Fp, x ∉ 𝒪[(D.s.atP p).Fp] →
    (((Loc.resChar p : ℕ) : (D.s.atP p).Fp) * x)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]

def FpDegCof : Prop :=
  ∀ D : Formalism.BasicNotions.D7, ∀ᶠ p in Filter.cofinite,
    haveI := (D.s.atP p).ellPrime
    ¬ (Loc.resChar p ∣ Module.finrank ℚ_[Loc.resChar p] (D.s.atP p).Fp)

end PI.UnitaryGroupMassFormula.CntFormula
