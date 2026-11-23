import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalModelsSplitCofinite

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SelfDualCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ L : LocSp D M,
      ∀ᶠ p in Filter.cofinite, (L.H p).IsSelfDual (lattice₂ L p (VS D).L0)

def DeltaUnitCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ᶠ p in Filter.cofinite, δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]

def IotaIntCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (x : D.host.E), ∀ᶠ p in Filter.cofinite, (D.s.atP p).ιE x ∈ (D.s.atP p).O

def DetGaNe : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D), GZ T T' Z ≠ 0 → (Ga T T' Z).det ≠ 0

def GaCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (T T' : D.host.E) (Z : MatZ D), (Ga T T' Z).det ≠ 0 →
      ∀ᶠ p in Filter.cofinite, (∀ a b, GaPlus M δ p T T' Z a b ∈ (M p).L.O) ∧
        ∃ y ∈ (M p).L.O, (GaPlus M δ p T T' Z).det * y = 1

end PI.UnitaryGroupMassFormula.CntFormula
