import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NChartP
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

def ExpChart : Prop :=
  ∀ k r : ℕ, Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1 =
    ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) •
      (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))).map (fun t => WlocSk.NB.phi0 t.1 t.2)

end Formalism.L2.SG.Pf.NcReal.JX
