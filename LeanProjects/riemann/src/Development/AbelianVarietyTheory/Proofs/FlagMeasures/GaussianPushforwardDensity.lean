import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean.ProdDensity

open GlobalTheory.GaussMean.Density Filter Topology

theorem integral_lt_eq {n : ℕ} (ε : Fin n → Bool) {a : ℝ} (ha : a ≠ 0) :
    ∫ y in {y : Fin n → ℂ | qEps ε y < a}, gauss y = cdf ε a := by
  apply le_antisymm
  · exact setIntegral_mono_set (integrable_gauss n).integrableOn
      (Filter.Eventually.of_forall fun y => (gauss_pos y).le)
      (HasSubset.Subset.eventuallyLE fun y (hy : qEps ε y < a) => hy.le)
  · have hc : Tendsto (cdf ε) (𝓝[<] a) (𝓝 (cdf ε a)) :=
      (differentiableAt_cdf ε ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hc ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < a)
    exact setIntegral_mono_set (integrable_gauss n).integrableOn
      (Filter.Eventually.of_forall fun y => (gauss_pos y).le)
      (HasSubset.Subset.eventuallyLE fun y (hy : qEps ε y ≤ t) => lt_of_le_of_lt hy ht)

theorem integral_Icc_eq {n : ℕ} (ε : Fin n → Bool) {a c : ℝ} (ha : a ≠ 0) (hac : a ≤ c) :
    ∫ y in qEps ε ⁻¹' Set.Icc a c, gauss y = cdf ε c - cdf ε a := by
  have hm : MeasurableSet {y : Fin n → ℂ | qEps ε y < a} :=
    measurableSet_lt (continuous_qEps ε).measurable measurable_const
  have h := integral_diff hm ((integrable_gauss n).integrableOn (s := {y | qEps ε y ≤ c}))
    (fun y (hy : qEps ε y < a) => show qEps ε y ≤ c by linarith)
  rw [integral_lt_eq ε ha] at h
  rw [cdf, ← h]
  congr 2
  ext y
  simp [and_comm]

theorem integral_box {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) (a c : ι → ℝ) (ha : ∀ v, a v ≠ 0)
    (hac : a ≤ c) :
    ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' Set.Icc a c, ∏ v, gauss (y v) =
      ∏ v, (cdf (ε v) (c v) - cdf (ε v) (a v)) := by
  have hm : MeasurableSet ((fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' Set.Icc a c) :=
    measurableSet_Icc.preimage
      (continuous_pi fun v => (continuous_qEps (ε v)).comp (continuous_apply v)).measurable
  rw [← integral_indicator hm, ← Finset.prod_congr rfl fun v _ => integral_Icc_eq (ε v) (ha v) (hac v),
    ← Finset.prod_congr rfl fun v _ => integral_indicator
      (measurableSet_Icc.preimage (continuous_qEps (ε v)).measurable),
    ← integral_fintype_prod_volume_eq_prod]
  congr 1
  funext y
  by_cases hy : y ∈ (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' Set.Icc a c
  · rw [Set.indicator_of_mem hy]
    exact Finset.prod_congr rfl fun v _ => (Set.indicator_of_mem (s := qEps (ε v) ⁻¹' Set.Icc (a v) (c v))
      ⟨hy.1 v, hy.2 v⟩ _).symm
  · rw [Set.indicator_of_notMem hy]
    obtain ⟨v, hv⟩ : ∃ v, y v ∉ qEps (ε v) ⁻¹' Set.Icc (a v) (c v) := by
      by_contra! h
      exact hy ⟨fun v => (h v).1, fun v => (h v).2⟩
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (Set.indicator_of_notMem hv _)).symm

theorem tendsto_mean_cube {ι : Type} [Fintype ι] {G : (ι → ℝ) → ℂ} (hG : Continuous G) (b : ι → ℝ) :
    Tendsto (fun r : ℝ => (r ^ Fintype.card ι)⁻¹ • ∫ x in Set.Icc b (fun v => b v + r), G x) (𝓝[>] 0)
      (𝓝 (G b)) := by
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨d, hd, hδ⟩ := Metric.continuousAt_iff.1 (hG.continuousAt (x := b)) (e / 2) (half_pos he)
  filter_upwards [Ioo_mem_nhdsGT hd] with r hr
  have hr0 := hr.1
  have hk : 0 < r ^ Fintype.card ι := pow_pos hr0 _
  have hvol : volume.real (Set.Icc b (fun v => b v + r)) = r ^ Fintype.card ι := by
    rw [Measure.real, Real.volume_Icc_pi_toReal (fun v => by simp [hr0.le])]
    simp
  have hfin : volume (Set.Icc b (fun v => b v + r)) < ⊤ := isCompact_Icc.measure_lt_top
  have h1 : ∫ x in Set.Icc b (fun v => b v + r), (G x - G b) =
      (∫ x in Set.Icc b (fun v => b v + r), G x) - (r ^ Fintype.card ι) • G b := by
    rw [integral_sub hG.continuousOn.integrableOn_Icc continuousOn_const.integrableOn_Icc,
      setIntegral_const, hvol]
  have h2 : ‖∫ x in Set.Icc b (fun v => b v + r), (G x - G b)‖ ≤ e / 2 * r ^ Fintype.card ι := by
    rw [← hvol]
    refine norm_setIntegral_le_of_norm_le_const hfin fun x hx => ?_
    rw [← dist_eq_norm]
    refine (hδ (lt_of_le_of_lt ?_ hr.2)).le
    rw [dist_pi_le_iff hr0.le]
    intro v
    have h3 := hx.1 v
    have h4 := hx.2 v
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have h3 : (r ^ Fintype.card ι)⁻¹ • (∫ x in Set.Icc b (fun v => b v + r), G x) - G b =
      (r ^ Fintype.card ι)⁻¹ • ∫ x in Set.Icc b (fun v => b v + r), (G x - G b) := by
    rw [h1, smul_sub, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  rw [dist_eq_norm, h3, norm_smul, Real.norm_of_nonneg (inv_pos.2 hk).le, inv_mul_lt_iff₀ hk]
  nlinarith

theorem density_eq_prod (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (G : (ι → ℝ) → ℂ)
    (hG : Continuous G)
    (h : ∀ S : Set (ι → ℝ), IsCompact S →
      ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' S, ((∏ v, gauss (y v) : ℝ) : ℂ) =
        ∫ b in S, G b)
    (b : ι → ℝ) (hb : ∀ v, b v ≠ 0) : G b = ((∏ v, gaussDens (ε v) (b v) : ℝ) : ℂ) := by
  have h1 : Tendsto (fun r : ℝ => ∏ v, r⁻¹ • (cdf (ε v) (b v + r) - cdf (ε v) (b v))) (𝓝[>] 0)
      (𝓝 (∏ v, gaussDens (ε v) (b v))) :=
    tendsto_finset_prod _ fun v _ =>
      (differentiableAt_cdf (ε v) (hb v)).hasDerivAt.tendsto_slope_zero_right
  have h2 := (Complex.continuous_ofReal.tendsto _).comp h1
  refine tendsto_nhds_unique (tendsto_mean_cube hG b) (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [← h _ isCompact_Icc, integral_complex_ofReal, integral_box ε b _ hb (fun v => by simp [hr.le])]
  simp [Finset.prod_mul_distrib]

end GlobalTheory.GaussMean.ProdDensity
