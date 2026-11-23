import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.L2Limit

theorem norm_sub_sq_le (a : ℕ → ℂ) (m k : ℕ) :
    ‖a m - a (k + m)‖ ^ 2 ≤ 2 / 2 ^ m *
      ∑ i ∈ Finset.range k, 2 ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 := by
  have htel : a m - a (k + m) = ∑ i ∈ Finset.range k, (a (i + m) - a (i + m + 1)) := by
    have := Finset.sum_range_sub' (fun i => a (i + m)) k
    simp only [zero_add] at this
    rw [← this]; exact Finset.sum_congr rfl fun i _ => by rw [add_right_comm]
  have h1 : ‖a m - a (k + m)‖ ≤ ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ := by
    rw [htel]; exact norm_sum_le _ _
  have hg : ∀ i ∈ Finset.range k, (0:ℝ) < (1/2) ^ (i + m) := fun i _ => by positivity
  have h2 := Finset.sq_sum_div_le_sum_sq_div (Finset.range k)
    (fun i => ‖a (i + m) - a (i + m + 1)‖) hg
  have hsg : ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) ≤ 2 / 2 ^ m := by
    have : ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) =
        (1/2) ^ m * ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
    rw [this]
    have := sum_geometric_two_le k
    have h2m : (0:ℝ) < (1/2) ^ m := by positivity
    calc (1/2:ℝ) ^ m * ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i ≤ (1/2) ^ m * 2 :=
          mul_le_mul_of_nonneg_left this h2m.le
      _ = 2 / 2 ^ m := by rw [one_div_pow]; ring
  have hsum_pos : 0 < ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) ∨ k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.sum_pos (fun i hi => hg i hi) ⟨0, by simp [h]⟩)
  rcases hsum_pos with hpos | hk
  · have h3 : (∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖) ^ 2 ≤
        (∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m)) *
          ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ ^ 2 / (1/2) ^ (i + m) := by
      rwa [div_le_iff₀ hpos, mul_comm] at h2
    have h4 : ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ ^ 2 / (1/2) ^ (i + m) =
        ∑ i ∈ Finset.range k, 2 ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_div_pow, div_div_eq_mul_div, div_one, mul_comm]
    rw [h4] at h3
    have hn : 0 ≤ ∑ i ∈ Finset.range k, (2:ℝ) ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    calc ‖a m - a (k + m)‖ ^ 2 ≤ (∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_right hsg hn
  · subst hk; simp

theorem tendsto_of_summable (a : ℕ → ℂ)
    (hs : Summable (fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2)) :
    ∃ L, Tendsto a atTop (𝓝 L) ∧ ∀ m, ‖a m - L‖ ^ 2 ≤
      2 / 2 ^ m * ∑' k, (2:ℝ) ^ (k + m) * ‖a (k + m) - a (k + m + 1)‖ ^ 2 := by
  set c : ℕ → ℝ := fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2 with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by positivity
  have hfin : ∀ m k, ‖a m - a (k + m)‖ ^ 2 ≤ 2 / 2 ^ m * ∑' i, c (i + m) := by
    intro m k
    refine (norm_sub_sq_le a m k).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Summable.sum_le_tsum _ (fun i _ => hc0 _) ((summable_nat_add_iff m).mpr hs)
  have htail := tendsto_sum_nat_add c
  have hcau : CauchySeq a := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev : ∀ᶠ m in atTop, 2 * ∑' i, c (i + m) < ε ^ 2 := by
      have := htail.const_mul 2
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm⟩ := hev.exists_forall_of_atTop
    refine ⟨m, fun N hN => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, N = k + m := ⟨N - m, by omega⟩
    have h1 := hfin m k
    have h2 : 2 / 2 ^ m * ∑' i, c (i + m) ≤ 2 * ∑' i, c (i + m) := by
      refine mul_le_mul_of_nonneg_right ?_ (tsum_nonneg fun i => hc0 _)
      exact div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
    have h3 : dist (a (k + m)) (a m) ^ 2 < ε ^ 2 := by
      rw [dist_eq_norm, norm_sub_rev]; linarith [hm m le_rfl]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨L, hL, fun m => ?_⟩
  have hlim : Tendsto (fun k => ‖a m - a (k + m)‖ ^ 2) atTop (𝓝 (‖a m - L‖ ^ 2)) :=
    (((hL.comp (tendsto_add_atTop_nat m)).const_sub (a m)).norm).pow 2
  exact le_of_tendsto' hlim fun k => hfin m k

end GlobalTheory.L2Limit

namespace GlobalTheory.L2Limit

section
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

open Classical in

noncomputable def limSec (F : ℕ → ι → Y → ℂ) : ι → Y → ℂ := fun i y =>
  if ∃ c, Tendsto (fun m => F m i y) atTop (𝓝 c) then limUnder atTop (fun m => F m i y) else 0

theorem limSec_eq (F : ℕ → ι → Y → ℂ) (i : ι) (y : Y) {c : ℂ}
    (h : Tendsto (fun m => F m i y) atTop (𝓝 c)) : limSec F i y = c := by
  unfold limSec; rw [if_pos ⟨c, h⟩]; exact h.limUnder_eq

theorem limSec_trans (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (i j : ι) (y : Y) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : limSec F i y = A.g la i j y * limSec F j y := by
  have hg := A.g_ne la i j y hi hj
  have hseq : (fun m => F m i y) = fun m => A.g la i j y * F m j y :=
    funext fun m => (hF m).2 i j y hi hj
  by_cases hc : ∃ c, Tendsto (fun m => F m j y) atTop (𝓝 c)
  · obtain ⟨c, hc⟩ := hc
    rw [limSec_eq F j y hc, limSec_eq F i y (by rw [hseq]; exact hc.const_mul _)]
  · have hc' : ¬ ∃ c, Tendsto (fun m => F m i y) atTop (𝓝 c) := by
      rintro ⟨c, hc'⟩
      apply hc
      refine ⟨(A.g la i j y)⁻¹ * c, ?_⟩
      have h2 : Tendsto (fun m => A.g la i j y * F m j y) atTop (𝓝 c) := by
        rw [← hseq]; exact hc'
      have := h2.const_mul (A.g la i j y)⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hg] using this
    unfold limSec
    rw [if_neg hc, if_neg hc', mul_zero]

theorem limSec_aemeas (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (i : ι) :
    AEMeasurable (limSec F i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target) := by
  classical
  set T := (A.chart i).target with hTdef
  have hT : MeasurableSet T := (A.chart i).open_target.measurableSet
  let G : ℕ → V n → ℂ := fun m => T.piecewise (F m i ∘ (A.chart i).symm) 0
  have hG : ∀ m, StronglyMeasurable (G m) := fun m =>
    (ContinuousOn.measurable_piecewise ((hF m).1 i).continuousOn continuousOn_const
      hT).stronglyMeasurable
  have hS := StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hG
  have hL := StronglyMeasurable.limUnder (l := atTop) hG
  have hmeas : StronglyMeasurable ({v | ∃ c, Tendsto (fun m => G m v) atTop (𝓝 c)}.piecewise
      (fun v => limUnder atTop (fun m => G m v)) (fun _ => (0:ℂ))) :=
    StronglyMeasurable.piecewise hS hL stronglyMeasurable_const
  refine hmeas.measurable.aemeasurable.congr ?_
  refine (ae_restrict_iff' hT).mpr (Eventually.of_forall fun v hv => ?_)
  have hGv : (fun m => G m v) = fun m => F m i ((A.chart i).symm v) :=
    funext fun m => by simp only [G, Set.piecewise_eq_of_mem _ _ _ hv, Function.comp_apply]
  simp only [Set.piecewise, Set.mem_setOf_eq, hGv, Function.comp_apply, limSec]

theorem measurable_step (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (j : ℕ) :
    Measurable (fun y => ENNReal.ofReal (A.nsq la (F j - F (j + 1)) y)) :=
  ENNReal.measurable_ofReal.comp (A.aap_continuous_nsq la (F j - F (j + 1)) (fun i k y hi hk => by
      simp only [Pi.sub_apply]; rw [(hF j).2 i k y hi hk, (hF (j + 1)).2 i k y hi hk]; ring)
    (fun i => ((hF j).1 i).continuousOn.sub ((hF (j + 1)).1 i).continuousOn)).measurable

end

theorem exists_l2_limit : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (F : ℕ → ι → Y → ℂ) (K : ℝ), 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → ∃ f : ι → Y → ℂ, (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g (A.kap + la) i j y * f j y) ∧ (∀ i, AEMeasurable (f i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target)) ∧ ∀ m, n0 A la (F m - f) ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
  intro n Y _ _ _ _ _ ι La _ A la F K hK hF hn
  set L := A.kap + la with hLdef
  set e : ℕ → Y → ℝ≥0∞ := fun j y => ENNReal.ofReal (A.nsq L (F j - F (j + 1)) y) with he_def
  have he : ∀ j, Measurable (e j) := measurable_step A L F hF
  have hint : ∀ j, ∫⁻ y, e j y ∂A.mu ≤ ENNReal.ofReal (K / 4 ^ j) := hn
  set S : ℕ → Y → ℝ≥0∞ := fun m y => ∑' k, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y with hSdef
  have hSm : ∀ m, Measurable (S m) := fun m =>
    Measurable.ennreal_tsum fun k => measurable_const.mul (he _)
  have hSint : ∀ m, ∫⁻ y, S m y ∂A.mu ≤ ENNReal.ofReal (K / 2 ^ m * 2) := by
    intro m
    show ∫⁻ y, ∑' k, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y ∂A.mu ≤ _
    rw [lintegral_tsum fun k => ((he (k + m)).const_mul _).aemeasurable]
    calc ∑' k, ∫⁻ y, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y ∂A.mu
        = ∑' k, ENNReal.ofReal (2 ^ (k + m)) * ∫⁻ y, e (k + m) y ∂A.mu := by
          congr 1; ext k; exact lintegral_const_mul _ (he _)
      _ ≤ ∑' k, ENNReal.ofReal (2 ^ (k + m)) * ENNReal.ofReal (K / 4 ^ (k + m)) :=
          ENNReal.tsum_le_tsum fun k => by gcongr; exact hint _
      _ = ∑' k, ENNReal.ofReal (K / 2 ^ m * (1 / 2) ^ k) := by
          congr 1; ext k
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (4:ℝ) ^ (k + m) = 2 ^ (k + m) * 2 ^ (k + m) by rw [← mul_pow]; norm_num]
          rw [pow_add, one_div_pow]; field_simp
      _ = ENNReal.ofReal (∑' k, K / 2 ^ m * (1 / 2) ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
            (summable_geometric_two.mul_left _)).symm
      _ = ENNReal.ofReal (K / 2 ^ m * 2) := by rw [tsum_mul_left, tsum_geometric_two]
  have hfin : ∀ᵐ y ∂A.mu, S 0 y < ⊤ :=
    ae_lt_top (hSm 0) ((hSint 0).trans_lt ENNReal.ofReal_lt_top).ne
  have hpt : ∀ m, ∀ᵐ y ∂A.mu, ENNReal.ofReal (A.nsq L (F m - limSec F) y) ≤
      ENNReal.ofReal (2 / 2 ^ m) * S m y := by
    intro m
    filter_upwards [hfin] with y hy
    set p := A.pick y
    set E := Real.exp (-A.ph L p y) with hE
    have hEpos : 0 < E := Real.exp_pos _
    set a : ℕ → ℂ := fun j => F j p y with ha
    have he_eq : ∀ j, e j y = ENNReal.ofReal (‖a j - a (j + 1)‖ ^ 2 * E) := fun j => rfl
    set b : ℕ → ℝ := fun k => 2 ^ k * (‖a k - a (k + 1)‖ ^ 2 * E) with hb_def
    have hb0 : ∀ k, 0 ≤ b k := fun k => by positivity
    have hSb : ∀ m', S m' y = ∑' k, ENNReal.ofReal (b (k + m')) := by
      intro m'
      simp only [hSdef, he_eq]
      congr 1; ext k
      rw [← ENNReal.ofReal_mul (by positivity)]
    have hb : Summable b := by
      have h0 := hSb 0
      simp only [add_zero] at h0
      have hs := ENNReal.summable_toReal (h0 ▸ hy.ne)
      refine hs.congr fun k => ?_
      exact ENNReal.toReal_ofReal (hb0 k)
    have hb' : Summable (fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2) := by
      refine (hb.div_const E).congr fun k => ?_
      simp only [hb_def]; field_simp
    obtain ⟨Lm, hLm, hbd⟩ := tendsto_of_summable a hb'
    have hf : limSec F p y = Lm := limSec_eq F p y hLm
    have hnsq : A.nsq L (F m - limSec F) y = ‖a m - Lm‖ ^ 2 * E := by
      show ‖F m p y - limSec F p y‖ ^ 2 * E = _
      rw [hf]
    rw [hnsq, hSb m, ← ENNReal.ofReal_tsum_of_nonneg (fun k => hb0 _)
      ((summable_nat_add_iff m).mpr hb), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_right (hbd m) hEpos.le
    calc ‖a m - Lm‖ ^ 2 * E
        ≤ 2 / 2 ^ m * (∑' k, (2:ℝ) ^ (k + m) * ‖a (k + m) - a (k + m + 1)‖ ^ 2) * E := this
      _ = 2 / 2 ^ m * ∑' k, b (k + m) := by
          rw [mul_assoc, ← tsum_mul_right]
          congr 2; ext k; simp only [hb_def]; ring
  refine ⟨limSec F, fun i j y hi hj => limSec_trans A L F hF i j y hi hj,
    fun i => limSec_aemeas A L F hF i, fun m => ?_⟩
  calc n0 A la (F m - limSec F) = ∫⁻ y, ENNReal.ofReal (A.nsq L (F m - limSec F) y) ∂A.mu := rfl
    _ ≤ ∫⁻ y, ENNReal.ofReal (2 / 2 ^ m) * S m y ∂A.mu := lintegral_mono_ae (hpt m)
    _ = ENNReal.ofReal (2 / 2 ^ m) * ∫⁻ y, S m y ∂A.mu := lintegral_const_mul _ (hSm m)
    _ ≤ ENNReal.ofReal (2 / 2 ^ m) * ENNReal.ofReal (K / 2 ^ m * 2) := by gcongr; exact hSint m
    _ = ENNReal.ofReal (4 * K / 4 ^ m) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show (4:ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
      field_simp; ring

end GlobalTheory.L2Limit
