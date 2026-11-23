import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.BoundsChain
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.BoundsSum

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

theorem lw_nonneg' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    0 ≤ lw w := by
  unfold lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

end Formalism.DivisionValues
