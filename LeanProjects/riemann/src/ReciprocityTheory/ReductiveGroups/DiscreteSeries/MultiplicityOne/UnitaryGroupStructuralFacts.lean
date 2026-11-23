import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def UnitaryGroupStructuralFacts : Prop :=
  ReciprocityTheory.ChartRestriction.DS.Xi.InductiveHeisenbergInputs ∧ RealPlaceDataExists ∧ RankOneCoord ∧ BigCellFactor ∧ UWbFacts ∧ ConjHaar ∧ LemmaBFromXi ∧
    StepJCont ∧ StepPhBound ∧ StepRegBound ∧ StepRegAverage ∧ StepUnfold ∧ AeFromTests ∧ DilJacAll ∧ IntNormB ∧
    Formalism.QuantumDeterminants.UWNormal ∧ Formalism.QuantumDeterminants.EllAdd ∧ Formalism.QuantumDeterminants.NSubgroup

end ReciprocityTheory.ChartRestriction.DS.Mult1
