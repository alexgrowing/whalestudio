import Formalism.PeriodIntegrals.FinExtTop

noncomputable section

namespace PI.UnitaryGroupMassFormula.FinExtTop

open PI.FinExtTop

def S1 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'],
    (ℓ : O) ≠ 0 →
    ∃ (_ : Algebra ℤ_[ℓ] O') (_ : IsScalarTower ℤ_[ℓ] O O') (_ : Module.Finite ℤ_[ℓ] O'),
      Function.Injective (algebraMap ℤ_[ℓ] O')

def S2 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'],
    PadicCoeff ℓ O → @PadicCoeff ℓ O' _ _ _ (moduleTopology O O')

def S3 : Prop :=
  ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [TopologicalSpace O'],
    IsAdic (IsLocalRing.maximalIdeal O') →
    ∃ (_ : TopologicalSpace (FractionRing O')) (_ : IsTopologicalAddGroup (FractionRing O'))
      (_ : ContinuousSMul O' (FractionRing O')), FracTop O'

def S4 : Prop :=
  ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [TopologicalSpace O']
    [IsTopologicalRing O'] [T2Space O'] (X' d : Type) [Fintype d] [DecidableEq d]
    (R' : Subalgebra O' (X' → Matrix d d (FractionRing O'))), Module.Finite O' R' →
    ∃ (_ : TopologicalSpace R') (_ : IsModuleTopology O' R'),
      IsTopologicalAddGroup R' ∧ ContinuousConstSMul O' R' ∧ ContinuousMul R' ∧
      IsTopologicalRing R' ∧ IsFGTop O' R'

end PI.UnitaryGroupMassFormula.FinExtTop
