import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.LatticeCountGen

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

variable (K : Type) [Field K] [NumberField K]

theorem measurableSet_box (r : InfinitePlace K → ℝ) : MeasurableSet (box K r) := by
  have : box K r = ⋂ w, {y | normAtPlace w y < r w} := by
    ext y; simp [box]
  rw [this]
  exact MeasurableSet.iInter fun w =>
    measurableSet_lt (continuous_normAtPlace w).measurable measurable_const

theorem measurableSet_hit (ρ : ℝ) (x : mixedSpace K) : MeasurableSet (hit K ρ x) := by
  have : hit K ρ x = ⋂ w, {y | normAtPlace w y * normAtPlace w x < ρ} := by
    ext y; simp [hit]
  rw [this]
  exact MeasurableSet.iInter fun w =>
    measurableSet_lt ((continuous_normAtPlace w).measurable.mul_const _) measurable_const

theorem measurableSet_shell : MeasurableSet (shell K) := by
  have : shell K = fundamentalCone K ∩
      ({y | 1 / 2 < mixedEmbedding.norm y} ∩ {y | mixedEmbedding.norm y ≤ 1}) := by
    ext y
    simp only [shell, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [this]
  exact (measurableSet_fundamentalCone K).inter
    ((measurableSet_lt measurable_const (mixedEmbedding.continuous_norm K).measurable).inter
      (measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const))

variable {K}

theorem normAtPlace_pos_of_norm_pos {y : mixedSpace K} (hy : 0 < mixedEmbedding.norm y)
    (w : InfinitePlace K) : 0 < normAtPlace w y := by
  refine lt_of_le_of_ne (normAtPlace_nonneg w y) fun h => ?_
  exact hy.ne' (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, h.symm⟩)

theorem prod_radius (ρ : ℝ) (y : mixedSpace K) :
    ∏ w : InfinitePlace K, (ρ / (2 * normAtPlace w y)) ^ mult w
      = (ρ / 2) ^ Module.finrank ℚ K / mixedEmbedding.norm y := by
  rw [mixedEmbedding.norm_apply, ← sum_mult_eq, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← div_pow, div_div]

theorem mem_hit_of_mem_sub {ρ : ℝ} {y x : mixedSpace K} (hy : 0 < mixedEmbedding.norm y)
    (hx : x ∈ box K (fun w => ρ / (2 * normAtPlace w y)) -
      box K (fun w => ρ / (2 * normAtPlace w y))) : y ∈ hit K ρ x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.mp hx
  intro w
  have hw := normAtPlace_pos_of_norm_pos hy w
  have h1 : normAtPlace w (a - b) ≤ normAtPlace w a + normAtPlace w b := by
    rw [sub_eq_add_neg]
    refine (normAtPlace_add_le w a (-b)).trans ?_
    rw [normAtPlace_neg]
  have ha' : normAtPlace w a < ρ / (2 * normAtPlace w y) := ha w
  have hb' : normAtPlace w b < ρ / (2 * normAtPlace w y) := hb w
  have h2 : normAtPlace w (a - b) < ρ / normAtPlace w y := by
    have : ρ / (2 * normAtPlace w y) + ρ / (2 * normAtPlace w y) = ρ / normAtPlace w y := by
      field_simp
      ring
    linarith
  rw [lt_div_iff₀ hw] at h2
  rw [mul_comm]
  exact h2

theorem count_pointwise (hB : BoxVolume) (J : (Ideal (𝓞 K))⁰) {ρ : ℝ} (hρ : 0 < ρ)
    {y : mixedSpace K} (hy : y ∈ shell K) :
    vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) ≤
      (∑' x : lat K J, (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y) *
        ENNReal.ofReal (ZLattice.covolume (lat K J)) := by
  have hy0 : 0 < mixedEmbedding.norm y := lt_trans (by norm_num) hy.2.1
  set r : InfinitePlace K → ℝ := fun w => ρ / (2 * normAtPlace w y) with hr
  have hrpos : ∀ w, 0 < r w := fun w =>
    div_pos hρ (mul_pos two_pos (normAtPlace_pos_of_norm_pos hy0 w))
  have hvol := hB K r hrpos
  rw [hr, prod_radius] at hvol
  have hcount := latticeCount K (lat K J) (box K r) (measurableSet_box K r)
  have h1 : vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) ≤ volume (box K r) := by
    rw [hr, hvol]
    gcongr
    rw [le_div_iff₀ hy0]
    have hp : 0 ≤ (ρ / 2) ^ Module.finrank ℚ K := by positivity
    nlinarith [hy.2.2]
  refine h1.trans (hcount.trans ?_)
  gcongr with x
  by_cases hx : (x : mixedSpace K) ∈ box K r - box K r
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (mem_hit_of_mem_sub hy0 hx)]
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

theorem countIntegral_of (hB : BoxVolume) : CountIntegral := by
  intro K _ _ J ρ hρ
  have hm : ∀ x : lat K J, Measurable
      (fun y => (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y) :=
    fun x => measurable_const.indicator (measurableSet_hit K ρ x)
  calc vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) * volume (shell K)
      = ∫⁻ _ in shell K, vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ y in shell K,
          (∑' x : lat K J, (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y) *
            ENNReal.ofReal (ZLattice.covolume (lat K J)) :=
        setLIntegral_mono' (measurableSet_shell K) fun y hy => count_pointwise hB J hρ hy
    _ = (∫⁻ y in shell K,
          (∑' x : lat K J, (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y)) *
            ENNReal.ofReal (ZLattice.covolume (lat K J)) :=
        lintegral_mul_const _ (Measurable.tsum hm)
    _ = (∑' x : lat K J, volume (shell K ∩ hit K ρ (x : mixedSpace K))) *
          ENNReal.ofReal (ZLattice.covolume (lat K J)) := by
        rw [lintegral_tsum fun x => (hm x).aemeasurable]
        congr 1
        refine tsum_congr fun x => ?_
        rw [lintegral_indicator_const (measurableSet_hit K ρ x), one_mul,
          Measure.restrict_apply (measurableSet_hit K ρ x), Set.inter_comm]
  exact le_rfl

end PI.Residue
