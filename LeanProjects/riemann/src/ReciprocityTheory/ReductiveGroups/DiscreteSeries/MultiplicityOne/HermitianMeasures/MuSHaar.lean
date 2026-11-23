import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.OrbitIntegralAbsConvergent
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSF

open MeasureTheory
open scoped NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

def MuSHaar : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN →
    Formalism.MainNotions.S.IsHaarOn (Sset k r z) (muSL μW μN) ∧
      ∀ μS : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (Sset k r z) μS → ∃ c : ℝ≥0, c ≠ 0 ∧ μS = c • muSL μW μN

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0
