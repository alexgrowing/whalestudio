import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.RootWeights.RaiseLowerPowCommutatorOnWeight
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsHighestCoordinateFunctional
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

def lowWt {n : ℕ} (mu : Fin n → ℤ) : Fin n → ℤ := fun a => mu (Fin.rev a)

def ContragredientIrreducibleGeneratedByHighestWeight : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' → IsIrrHW (dualOps E) (dualWt mu) v'

def DualFunctionalInjectiveOnLowestWeightSpace : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    (∀ x ∈ weightSp E (lowWt mu), v' x = 0 → x = 0) ∧ ∀ nu, nu ≠ lowWt mu → ∀ x ∈ weightSp E nu, v' x = 0

def LowestWeightExtremalVector : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V),
    IsIrrHW E mu v →
    ∃ w ∈ Delta (O := O) E v, w ∈ weightSp E (lowWt mu) ∧ ∃ u ∈ UZmon E, u w = v

def DeltaGeneratedByLowestWeightVector : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) →
    ∃ x0 ∈ Delta (O := O) E v, x0 ∈ weightSp E (lowWt mu) ∧ v' x0 = 1 ∧
      Delta (O := O) E v = Submodule.span O {x | ∃ u ∈ UZmon E, x = u x0}

def DeltaFinitelyGenerated : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) → (Delta (O := O) E v).FG

def NablaContragredientEqDualLatticeDelta : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) →
    Nabla (O := O) (dualOps E) (dualWt mu) v' =
      {φ | ∀ x ∈ Delta (O := O) E v, φ x ∈ Set.range (algebraMap O (KK O))}

def LatticeBiduality : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] (M : Submodule O V), M.FG →
    Submodule.span (KK O) (M : Set V) = ⊤ →
    (M : Set V) = {x | ∀ φ : Module.Dual (KK O) V, (∀ y ∈ M, φ y ∈ Set.range (algebraMap O (KK O))) →
      φ x ∈ Set.range (algebraMap O (KK O))}

end Formalism.MainNotions.G.ColumnFamilies
