import Mathlib
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhat

open NumberField IsDedekindDomain Topology Filter MeasureTheory NumberField.mixedEmbedding
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap Classical

namespace GroundTheory.Global

noncomputable section

open InfinitePlace InfinitePlace.Completion

section Completion

variable {K : Type*} [Field K]

theorem norm_isometryEquivRealOfIsReal {w : InfinitePlace K} (hw : w.IsReal) (z : w.Completion) :
    ‖isometryEquivRealOfIsReal hw z‖ = ‖z‖ :=
  (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) z

theorem norm_isometryEquivComplexOfIsComplex {w : InfinitePlace K} (hw : w.IsComplex)
    (z : w.Completion) : ‖isometryEquivComplexOfIsComplex hw z‖ = ‖z‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) z

theorem one_le_mult (w : InfinitePlace K) : (1 : ℝ) ≤ w.mult := by
  unfold InfinitePlace.mult
  split_ifs <;> norm_num

theorem mult_le_two (w : InfinitePlace K) : (w.mult : ℝ) ≤ 2 := by
  unfold InfinitePlace.mult
  split_ifs <;> norm_num

theorem lintegral_one_add_norm_rpow_neg_lt_top (w : InfinitePlace K) {r : ℝ} (hr : 2 < r) :
    ∫⁻ z, ENNReal.ofReal ((1 + ‖z‖) ^ (-r)) ∂infinitePlaceMeasure w < ∞ := by
  have hm : Measurable fun z : w.Completion ↦ ENNReal.ofReal ((1 + ‖z‖) ^ (-r)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_const.add continuous_norm).rpow_const fun z ↦
        Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg z)).ne').measurable
  by_cases hw : w.IsReal
  · rw [infinitePlaceMeasure_of_isReal hw,
      lintegral_map hm (isometryEquivRealOfIsReal hw).symm.continuous.measurable]
    have h : ∀ y : ℝ, ‖(isometryEquivRealOfIsReal hw).symm y‖ = ‖y‖ := fun y ↦ by
      rw [← norm_isometryEquivRealOfIsReal hw, IsometryEquiv.apply_symm_apply]
    simp_rw [h]
    exact finite_integral_one_add_norm (by simp; linarith)
  · have hc := not_isReal_iff_isComplex.1 hw
    rw [infinitePlaceMeasure_of_isComplex hc,
      lintegral_map hm (isometryEquivComplexOfIsComplex hc).symm.continuous.measurable]
    have h : ∀ y : ℂ, ‖(isometryEquivComplexOfIsComplex hc).symm y‖ = ‖y‖ := fun y ↦ by
      rw [← norm_isometryEquivComplexOfIsComplex hc, IsometryEquiv.apply_symm_apply]
    simp_rw [h]
    have : ((2 : ℝ≥0∞) • (volume : Measure ℂ)).IsAddHaarMeasure :=
      Measure.IsAddHaarMeasure.smul _ (by norm_num) (by simp)
    exact finite_integral_one_add_norm (by simp [Complex.finrank_real_complex]; linarith)

theorem lintegral_unitsMeasure_le {F : Type*} [NormedField F] [LocallyCompactSpace F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F) (m : ℕ)
    {g : F → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ u, g u ∂unitsMeasure μ m ≤ ∫⁻ z, ENNReal.ofReal (‖z‖ ^ m)⁻¹ * g z ∂μ := by
  have he := measurableEmbedding_units_val (F := F)
  calc ∫⁻ u, g u ∂unitsMeasure μ m
      = ∫⁻ z, g z ∂(Measure.map Units.val (unitsMeasure μ m)) := (he.lintegral_map g).symm
    _ = ∫⁻ z in Set.range Units.val, g z
          ∂(μ.withDensity fun x ↦ ENNReal.ofReal (‖x‖ ^ m)⁻¹) := by
        rw [unitsMeasure, he.map_comap]
    _ ≤ ∫⁻ z, g z ∂(μ.withDensity fun x ↦ ENNReal.ofReal (‖x‖ ^ m)⁻¹) :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ z, ENNReal.ofReal (‖z‖ ^ m)⁻¹ * g z ∂μ := by
        rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_density_unitsMeasure m) hg]
        rfl

def placeZetaBound (w : InfinitePlace K) (σ : ℝ) (k : ℕ) (z : (w.Completion)ˣ) : ℝ :=
  ‖(z : w.Completion)‖ ^ ((w.mult : ℝ) * σ) / (1 + ‖(z : w.Completion)‖) ^ k

theorem continuous_placeZetaBound (w : InfinitePlace K) {σ : ℝ} (hσ : 0 ≤ σ) (k : ℕ) :
    Continuous fun z : w.Completion ↦ ‖z‖ ^ ((w.mult : ℝ) * σ) / (1 + ‖z‖) ^ k :=
  (continuous_norm.rpow_const fun _ ↦ Or.inr (mul_nonneg (Nat.cast_nonneg _) hσ)).div
    ((continuous_const.add continuous_norm).pow k) fun _ ↦ by positivity

theorem integrable_placeZetaBound (w : InfinitePlace K) {σ : ℝ} (hσ : 1 ≤ σ) {k : ℕ}
    (hk : 2 * σ + 2 < k) : Integrable (placeZetaBound w σ k) (infinitePlaceUnitsMeasure w) := by
  have hG := continuous_placeZetaBound w (by linarith : (0 : ℝ) ≤ σ) k
  refine ⟨(hG.comp Units.continuous_val).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z ↦ by
    unfold placeZetaBound; positivity)]
  refine (lintegral_unitsMeasure_le (infinitePlaceMeasure w) w.mult
    (g := fun z ↦ ENNReal.ofReal (‖z‖ ^ ((w.mult : ℝ) * σ) / (1 + ‖z‖) ^ k))
    (ENNReal.measurable_ofReal.comp hG.measurable)).trans_lt ?_
  refine lt_of_le_of_lt (lintegral_mono fun z ↦ ?_)
    (lintegral_one_add_norm_rpow_neg_lt_top w (r := k - 2 * σ) (by linarith))
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hm1 := one_le_mult w
  have hm2 := mult_le_two w
  set t := ‖z‖
  have ht : 0 ≤ t := norm_nonneg _
  have ha : 1 ≤ 1 + t := by linarith
  have hapos : 0 < 1 + t := by linarith
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by positivity), zero_div, mul_zero]
    positivity
  · have e1 : (t ^ w.mult)⁻¹ * (t ^ ((w.mult : ℝ) * σ) / (1 + t) ^ k) =
        t ^ ((w.mult : ℝ) * σ - w.mult) * ((1 + t) ^ (k : ℝ))⁻¹ := by
      rw [← Real.rpow_natCast t w.mult, ← Real.rpow_natCast (1 + t) k, Real.rpow_sub hpos,
        div_eq_mul_inv, div_eq_mul_inv]
      ring
    have e2 : (1 + t) ^ (-((k : ℝ) - 2 * σ)) = (1 + t) ^ (2 * σ) * ((1 + t) ^ (k : ℝ))⁻¹ := by
      rw [← Real.rpow_neg hapos.le, ← Real.rpow_add hapos]
      congr 1
      ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc t ^ ((w.mult : ℝ) * σ - w.mult) ≤ (1 + t) ^ ((w.mult : ℝ) * σ - w.mult) :=
          Real.rpow_le_rpow ht (by linarith) (by nlinarith)
      _ ≤ (1 + t) ^ (2 * σ) := Real.rpow_le_rpow_of_exponent_le ha (by nlinarith)

end Completion

variable {K : Type*} [Field K] [NumberField K]

def infiniteZetaBound (σ : ℝ) (k : ℕ) (a : (InfiniteAdeleRing K)ˣ) : ℝ :=
  ∏ w : InfinitePlace K, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ) /
    (1 + ‖(a : InfiniteAdeleRing K) w‖) ^ k

theorem integrable_infiniteZetaBound {σ : ℝ} (hσ : 1 ≤ σ) {k : ℕ} (hk : 2 * σ + 2 < k) :
    Integrable (infiniteZetaBound (K := K) σ k) (infiniteIdeleMeasure K) := by
  have h := Integrable.fintype_prod_dep (𝕜 := ℝ) (f := fun w : InfinitePlace K ↦ placeZetaBound w σ k)
    (μ := fun w ↦ infinitePlaceUnitsMeasure w) fun w ↦ integrable_placeZetaBound w hσ hk
  rw [infiniteIdeleMeasure]
  refine (integrable_map_equiv (infiniteUnitsEquiv K).symm.toHomeomorph.toMeasurableEquiv _).2 ?_
  exact h

theorem norm_le_norm_homeomorphMixedSpace (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    ‖x w‖ ≤ ‖homeomorphMixedSpace K x‖ := by
  by_cases hw : w.IsReal
  · have h1 : (homeomorphMixedSpace K x).1 ⟨w, hw⟩ = isometryEquivRealOfIsReal hw (x w) := rfl
    calc ‖x w‖ = ‖(homeomorphMixedSpace K x).1 ⟨w, hw⟩‖ := by
          rw [h1, norm_isometryEquivRealOfIsReal]
      _ ≤ ‖(homeomorphMixedSpace K x).1‖ := norm_le_pi_norm _ _
      _ ≤ ‖homeomorphMixedSpace K x‖ := norm_fst_le _
  · have hc := not_isReal_iff_isComplex.1 hw
    have h1 : (homeomorphMixedSpace K x).2 ⟨w, hc⟩ =
        isometryEquivComplexOfIsComplex hc (x w) := rfl
    calc ‖x w‖ = ‖(homeomorphMixedSpace K x).2 ⟨w, hc⟩‖ := by
          rw [h1, norm_isometryEquivComplexOfIsComplex]
      _ ≤ ‖(homeomorphMixedSpace K x).2‖ := norm_le_pi_norm _ _
      _ ≤ ‖homeomorphMixedSpace K x‖ := norm_snd_le _

theorem exists_norm_schwartz_le_prod (φ : 𝓢(mixedSpace K, ℂ)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x : InfiniteAdeleRing K,
      ‖φ (homeomorphMixedSpace K x)‖ ≤ C * ∏ w, ((1 + ‖x w‖) ^ k)⁻¹ := by
  set d := Fintype.card (InfinitePlace K)
  set C := 2 ^ (k * d) *
    (Finset.Iic (k * d, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) φ
  refine ⟨C, by positivity, fun x ↦ ?_⟩
  set y := homeomorphMixedSpace K x
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k * d, 0)) le_rfl le_rfl φ y
  rw [norm_iteratedFDeriv_zero] at h1
  have hprod : ∏ w, (1 + ‖x w‖) ^ k ≤ (1 + ‖y‖) ^ (k * d) := by
    calc ∏ w, (1 + ‖x w‖) ^ k ≤ ∏ _w : InfinitePlace K, (1 + ‖y‖) ^ k :=
          Finset.prod_le_prod (fun w _ ↦ by positivity) fun w _ ↦
            pow_le_pow_left₀ (by positivity) (by linarith [norm_le_norm_homeomorphMixedSpace x w]) k
      _ = (1 + ‖y‖) ^ (k * d) := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hpos : 0 < ∏ w, (1 + ‖x w‖) ^ k := Finset.prod_pos fun w _ ↦ by positivity
  rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖φ y‖ * ∏ w, (1 + ‖x w‖) ^ k ≤ ‖φ y‖ * (1 + ‖y‖) ^ (k * d) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (1 + ‖y‖) ^ (k * d) * ‖φ y‖ := mul_comm _ _
    _ ≤ C := h1

end

end GroundTheory.Global
