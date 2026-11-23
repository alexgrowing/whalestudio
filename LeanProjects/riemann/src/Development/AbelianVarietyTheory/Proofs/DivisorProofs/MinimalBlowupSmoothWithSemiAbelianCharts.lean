import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionBlowupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChartSiegelNormalizedBlowupStatement

namespace GlobalTheory.SiegJoin

theorem chartSt5_holds : ChartSt5 :=
  fun g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j _ BD hM hB =>
    ⟨GlobalTheory.T.smoothOfRelativeDimension_blowAt_comp g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j BD hM hB,
      GlobalTheory.T.exists_preChart_siegel_normalizedBlowup g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j BD hM hB⟩

end GlobalTheory.SiegJoin
