import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMixedBoxCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeCountVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Metric
open scoped ENNReal NNReal

namespace MixedBoxCount

open scoped Classical in

theorem finite_box (F : Type) [Field F] [NumberField F] (La : Submodule ℤ (mixedSpace F))
    [DiscreteTopology La] (f : InfinitePlace F → ℝ) (hf : ∀ w, 0 < f w) :
    {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.Finite := by
  have hsub : {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w} ⊆
      closedBall 0 (∑ w, f w) ∩ (La : Set (mixedSpace F)) := by
    rintro y ⟨hyL, hy⟩
    refine ⟨?_, hyL⟩
    rw [mem_closedBall_zero_iff, norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun w _ => (hy w).trans ?_
    exact Finset.single_le_sum (fun v _ => (hf v).le) (Finset.mem_univ w)
  refine Set.Finite.subset ?_ hsub
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

open scoped Classical in

theorem normAtPlace_lt_of_mem (F : Type) [Field F] [NumberField F] (g : InfinitePlace F → ℝ≥0)
    {x : mixedSpace F} (hx : x ∈ convexBodyLT F g) (w : InfinitePlace F) : normAtPlace w x < g w := by
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw]
    have := hx.1 ⟨w, hw⟩ (Set.mem_univ _)
    simpa [mem_ball_zero_iff] using this
  · rw [normAtPlace_apply_of_isComplex hw]
    have := hx.2 ⟨w, hw⟩ (Set.mem_univ _)
    simpa [mem_ball_zero_iff] using this

end MixedBoxCount

open scoped Classical in

theorem MixedBoxCount.proof (h : LatticeCountVolume.Statement) : MixedBoxCount.Statement := by
  intro F _ _ La _ _ f hf
  have hfin := MixedBoxCount.finite_box F La f hf
  refine ⟨hfin, ?_⟩
  set B := {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w} with hB
  let g : InfinitePlace F → ℝ≥0 := fun w => ⟨f w / 2, (half_pos (hf w)).le⟩
  have hS : MeasurableSet (convexBodyLT F g) :=
    (MeasurableSet.univ_pi fun _ => measurableSet_ball).prod
      (MeasurableSet.univ_pi fun _ => measurableSet_ball)
  have hdiff : ∀ x ∈ convexBodyLT F g, ∀ y ∈ convexBodyLT F g,
      x - y ∈ {z : mixedSpace F | ∀ w, normAtPlace w z ≤ f w} := by
    intro x hx y hy w
    have h1 := MixedBoxCount.normAtPlace_lt_of_mem F g hx w
    have h2 := MixedBoxCount.normAtPlace_lt_of_mem F g hy w
    have h3 := normAtPlace_add_le w x (-y)
    rw [normAtPlace_neg, ← sub_eq_add_neg] at h3
    have : ((g w : ℝ≥0) : ℝ) = f w / 2 := rfl
    linarith
  have hle := h (mixedSpace F) volume La (convexBodyLT F g) _ hS hdiff
  have hset : {x : mixedSpace F | x ∈ La ∧ x ∈ {z : mixedSpace F | ∀ w, normAtPlace w z ≤ f w}} = B := rfl
  rw [hset, convexBodyLT_volume, ← hfin.cast_ncard_eq] at hle
  have hcpos := ZLattice.covolume_pos La volume
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hle
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hcpos.le, NNReal.coe_prod,
    NNReal.coe_pow, ENat.toENNReal_coe, ENNReal.toReal_natCast] at hreal
  have hg : ∀ w, ((g w : ℝ≥0) : ℝ) = f w / 2 := fun _ => rfl
  simp only [hg] at hreal
  have hNpos : 0 < B.ncard :=
    (Set.ncard_pos hfin).mpr ⟨0, La.zero_mem, fun w => by simp [(hf w).le]⟩
  have hN : (0 : ℝ) < (B.ncard : ℝ) := by exact_mod_cast hNpos
  have hc : (0 : ℝ) < (convexBodyLTFactor F : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (convexBodyLTFactor_ne_zero F))
  have hfac : ∀ w, 0 < (f w / 2) ^ mult w := fun w => pow_pos (half_pos (hf w)) _
  have hprod : 0 < ∏ w, (f w / 2) ^ mult w := Finset.prod_pos fun w _ => hfac w
  have hlog := Real.log_le_log (mul_pos hc hprod) hreal
  rw [Real.log_mul hc.ne' hprod.ne', Real.log_mul hN.ne' hcpos.ne',
    Real.log_prod (fun w _ => (hfac w).ne')] at hlog
  have hl : ∀ w, Real.log ((f w / 2) ^ mult w) = (mult w : ℝ) * Real.log (f w) - (mult w : ℝ) * Real.log 2 :=
    fun w => by rw [Real.log_pow, Real.log_div (hf w).ne' two_ne_zero, mul_sub]
  have hcast : (∑ w : InfinitePlace F, (mult w : ℝ)) = (Module.finrank ℚ F : ℝ) := by
    exact_mod_cast sum_mult_eq
  simp only [hl, Finset.sum_sub_distrib, ← Finset.sum_mul, hcast] at hlog
  linarith

end GroundTheory.Heights₂.Heights.Targets
