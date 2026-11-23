import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.AdmissibleAtRealPlace
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.WeightedL1OfL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDiagExists

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold
  ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

variable {k r : ℕ}

def cj (t : Mat k r) (x : Mt k r) : Mt k r := fun i j => (t⁻¹ * Matrix.of x * t) i j

def cjP (x y : Mt k r) : Mt k r := (Matrix.of x * Matrix.of y * (Matrix.of x)⁻¹ : Mat k r)

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down
