import Formalism.GaussJetBounds.OneLetterGaussJets.TheoremATwoFormsOfEntry
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.CompanionTheory
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.OneLetterUnramifiedBound
import Formalism.GaussJetBounds.OneLetterGaussJets.SizesRows7

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

theorem propSix7 : PropSix7 := proposition_six
theorem gain_dominates_oddLevel_sum : GainDominatesInnerSum := gain_ge_inner_sum
theorem normCor7 : NormCor7 := by
  intro l d _ hl hd he TT nu1 nu2 size k L w E pi y hpi0 hpi1 hk hw hE hD1 hD2 hy
  refine hy.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1.le ?_)
  have h6 := propSix7 l d hl hd he TT k (fun s => (Dl d TT nu1 size s : ℝ)) w E hk hw hE hD1 hD2
  have hsum : ∑ s ∈ TT, oddLevelGainSum l d TT nu1 nu2 s ≤ ∑ s ∈ TT, topTerm l d TT nu1 nu2 s :=
    Finset.sum_le_sum fun s _ => gain_dominates_oddLevel_sum l d (by omega) TT nu1 nu2 s
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith [h6.1, h6.2]
theorem oneLetterGauss7 : OneLetterGauss7 := one_letter_gauss_bound

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
