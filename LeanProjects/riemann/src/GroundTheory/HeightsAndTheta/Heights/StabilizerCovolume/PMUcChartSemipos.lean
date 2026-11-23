import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcLeviChart
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StAPrimeMarginCharts
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi)

theorem MUcChartSemipos.proof (hS : MUcSmooth.Statement) (hL : MUcLeviChart.Statement)
    (hA : APrimeMarginCharts.Statement) : MUcChartSemipos.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D H M w S
  obtain ⟨c, hc, hAc⟩ := hA II Ψ K ι Ω E D M S.B.toPotentialCharts
  refine ⟨c, hc, fun B p q t δ hs hl hqp => ⟨hS II Ψ K ι Ω E D H M w S B p q t hs, fun z hz u hu => ?_⟩⟩
  obtain ⟨k, hk⟩ := S.B.cover (M.proj z)
  have hk' : M.proj z ∈ S.B.mid k := S.B.inner_subset_mid k hk
  obtain ⟨v, hv, heq⟩ := hL II Ψ K ι Ω E D H M w S B p q t hs z hz u hu k hk'
  have h1 := hl k _ hk' v
  have h2 := hAc z hz u k hk' v hv
  show 0 ≤ levi _ z u
  rw [heq]
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hv2 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h1 hq, mul_le_mul_of_nonneg_left h2 hp,
    mul_le_mul_of_nonneg_right hqp hv2]

end GroundTheory.Heights₂.Heights.NineStatements
