import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFdGramCut
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6 Formalism.QuantumDeterminants.BesselUnitaryEquiv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

def UnipotentHaarConjInvariant : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∀ μ0 : Measure (Mt k r),
    B.IsHaarOn (C2.N0set k r z) μ0 → ∀ c ∈ UWset k r z, μ0.map (conjM c) = μ0

end PI.UnitaryGroupMassFormula.DLm.Gram
