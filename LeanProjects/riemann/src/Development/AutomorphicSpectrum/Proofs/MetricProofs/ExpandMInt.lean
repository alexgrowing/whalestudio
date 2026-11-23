import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSetStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.ExpandMInt

theorem expand_mInt : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X) (g : X → ℝ), IsOpen U → (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → (∀ T : Finset (Fin e), MIntegrable A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g) → MIntegrable A (fun i => P i + LocPot.ofFun (f i)) g ∧ mInt A (fun i => P i + LocPot.ofFun (f i)) g = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * mInt A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g := by
  intro e X _ _ _ A U P f Θ g hU hnull hP hΘ hf hT

  have hae : ∀ j, ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∈ (A.chart j).target →
      locDens A (fun i => P i + LocPot.ofFun (f i)) j y =
        ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
          locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
            LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
    intro j
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) (hnull j)
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hy
    refine ⟨hy.1, fun hyU => hy.2 ?_⟩
    exact GlobalTheory.T.local_density_inclusion_exclusion A U P f Θ hU hP hΘ hf j y ⟨hy.1, hyU⟩
  refine ⟨?_, ?_⟩
  · intro j K hK hKc
    have hsum : IntegrableOn (fun y => ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        (g ((A.chart j).symm y) * locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
            LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y)) K :=
      integrable_finsetSum _ fun T _ => (hT T j K hK hKc).const_mul _
    refine hsum.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae (hae j), ae_restrict_mem hKc.measurableSet] with y hy hyK
    rw [hy (hK hyK), Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  · unfold mInt
    split_ifs with h
    · unfold integralWith
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ fun T _ => (integrableOn_weight A h.some _ g (hT T) j).const_mul _]
      refine setIntegral_congr_ae (A.chart j).open_target.measurableSet ?_
      filter_upwards [hae j] with y hy hyt
      rw [hy hyt, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      ring
    · simp

end GlobalTheory.CompanionTheory.Metric.ExpandMInt
