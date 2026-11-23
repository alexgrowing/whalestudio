import Formalism.TruncatedSeriesCounting.LemmaDetPoly

open Formalism.NG

universe u v w

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem eta_determinant_comparison : BridgeDet.{u, v, w} := by
  intro hP hB O _ _ X' G _ T' d _ _ R' ρ hρ hR g _ _ Θ
  refine hB O X' T' d R' ?_ g Θ
  intro m a s
  exact hP O (FractionRing O) X' G d T' ρ hρ m (fun i => (a i : X' → Matrix d d (FractionRing O)))
    (fun i => hR _ (a i).2) s

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
