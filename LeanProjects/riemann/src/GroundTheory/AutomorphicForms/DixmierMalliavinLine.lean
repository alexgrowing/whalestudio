import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavinLineBounds
import GroundTheory.AutomorphicForms.DixmierMalliavinLineLimit

namespace GroundTheory.Automorphic

open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform

set_option linter.unusedSectionVars false

noncomputable section

namespace LineKernel

def radii (ε : ℝ) (j : ℕ) : ℝ := ε / 2 ^ (j + 3)

theorem radii_pos {ε : ℝ} (hε : 0 < ε) (j : ℕ) : 0 < radii ε j := by unfold radii; positivity

theorem Rs_radii_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) : Rs (radii ε) n ≤ ε / 2 := by
  have e : ∀ j, 2 * radii ε j = ε / 4 * (1 / 2) ^ j := by
    intro j; unfold radii; rw [pow_add, one_div_pow]; field_simp; norm_num
  unfold Rs
  simp_rw [e, ← Finset.mul_sum]
  have := sum_geometric_two_le (n + 1)
  nlinarith

def weight (M : ℕ → ℝ) (p : ℕ) : ℝ := if p = 0 then 1 else (1 / 2) ^ p / max 1 |M p|

theorem weight_pos (M : ℕ → ℝ) (p : ℕ) : 0 < weight M p := by
  unfold weight; split_ifs
  · exact one_pos
  · exact div_pos (by positivity) (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem weight_le_one (M : ℕ → ℝ) (p : ℕ) : weight M p ≤ 1 := by
  unfold weight; split_ifs
  · exact le_rfl
  · rw [div_le_one (lt_of_lt_of_le one_pos (le_max_left _ _))]
    exact (pow_le_one₀ (by norm_num) (by norm_num)).trans (le_max_left _ _)

theorem weight_mul_abs_le (M : ℕ → ℝ) (p : ℕ) :
    weight M p * |M p| ≤ (1 / 2) ^ p * max 1 |M 0| := by
  unfold weight; split_ifs with h
  · subst h; simp
  · have hm : 0 < max 1 |M p| := lt_of_lt_of_le one_pos (le_max_left _ _)
    calc (1 / 2) ^ p / max 1 |M p| * |M p| ≤ (1 / 2) ^ p := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hm]
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ ≤ (1 / 2) ^ p * max 1 |M 0| := le_mul_of_one_le_right (by positivity) (le_max_left _ _)

def Good (M : ℕ → ℝ) (ε : ℝ) (j : ℕ) (x : ℝ) : Prop :=
  0 < x ∧ (∀ p ∈ Finset.range (j + 2), 1 ≤ p →
      x⁻¹ * weight M (p - 1) ≤ (1 / 2) ^ (j + 1) * weight M p) ∧
    (∀ q ∈ Finset.range (2 * j + 3), ∀ t,
      ‖iteratedDeriv q (rem x (radii ε j)) t‖ ≤ (1 / 2) ^ j / (j + 2)) ∧
    exp (-x * radii ε j) ≤ (1 / 2) ^ j

theorem eventually_good (M : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ∀ᶠ x in atTop, Good M ε j x := by
  have hr := radii_pos hε j
  refine (eventually_gt_atTop 0).and (((eventually_all_finset _).2 fun p _ => ?_).and
    (((eventually_all_finset _).2 fun q _ => ?_).and ?_))
  · have hc : 0 < (1 / 2 : ℝ) ^ (j + 1) * weight M p := by
      have := weight_pos M p; positivity
    filter_upwards [eventually_ge_atTop (weight M (p - 1) / ((1 / 2) ^ (j + 1) * weight M p)),
      eventually_gt_atTop 0] with x hx hx0 _
    rw [inv_mul_le_iff₀ hx0]
    rw [div_le_iff₀ hc] at hx; linarith
  · exact eventually_norm_iteratedDeriv_rem_le hr q (by positivity)
  · have ht : Tendsto (fun x : ℝ => exp (-x * radii ε j)) atTop (𝓝 0) := by
      have := tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hr)
      refine this.congr fun x => ?_
      simp [neg_mul]
    exact ht.eventually (ge_mem_nhds (by positivity))

theorem integral_norm_le_of_support {f : ℝ → ℂ} (hf : Continuous f) {c D : ℝ} (hc : 0 ≤ c)
    (hs : support f ⊆ Icc 0 c) (hD : ∀ t ∈ Icc 0 c, ‖f t‖ ≤ D) : ∫ t, ‖f t‖ ≤ D * c := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc 0 c) fun t ht => by
    have : f t = 0 := by by_contra h; exact ht (hs h)
    simp [this]]
  calc ∫ t in Icc 0 c, ‖f t‖ ≤ ∫ t in Icc 0 c, D :=
        setIntegral_mono_on hf.norm.integrableOn_Icc (integrableOn_const (by simp) (by simp))
          measurableSet_Icc hD
    _ = D * c := by simp [hc, mul_comm]

theorem integrable_mul_of_support {φ K : ℝ → ℂ} (hφ : Continuous φ) (hK : Integrable K) {c : ℝ}
    (hs : support K ⊆ Icc 0 c) : Integrable fun u => φ u * K u := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 c) hφ.continuousOn
  refine Integrable.mono' (hK.norm.const_mul B) (hφ.aestronglyMeasurable.mul hK.aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  by_cases hu : K u = 0
  · simp [hu]
  · exact mul_le_mul_of_nonneg_right (hB u (hs hu)) (norm_nonneg _)

section Sequence

variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg

theorem good_pos (j : ℕ) : 0 < a j := (hg j).1

theorem coef_le_weight (n p : ℕ) : coef a n p ≤ weight M p := by
  refine coef_le_of (fun j => (hg j).1) (by simp [weight]) (fun p => (weight_pos M p).le)
    (fun n p hp hpn => (hg n).2.1 p (Finset.mem_range.2 (by omega)) hp) n p

theorem norm_iteratedDeriv_ρ_succ_le_half_pow (n k : ℕ) (hk : k ≤ n + 1) (t : ℝ) :
    ‖iteratedDeriv k (ρ a (radii ε) (n + 1)) t‖ ≤ (1 / 2) ^ (n + 1) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hS := fun q => norm_iteratedDeriv_rem_le (hr (n + 1)) q
  choose S hS0 hS using hS
  set δ : ℝ := (1 / 2) ^ (n + 1) / ((n + 1 : ℕ) + 2 : ℝ) with hδ
  set B : ℕ → ℝ := fun q => if q < 2 * (n + 1) + 3 then δ else
    2 ^ q * (1 + a (n + 1)) ^ q * exp (-a (n + 1) * radii ε (n + 1)) * S q with hB
  have hBq : ∀ q t, ‖iteratedDeriv q (rem (a (n + 1)) (radii ε (n + 1))) t‖ ≤ B q := by
    intro q t
    simp only [hB]
    split_ifs with hq
    · exact (hg (n + 1)).2.2.1 q (Finset.mem_range.2 hq) t
    · exact hS q (a (n + 1)) (ha _).le t
  refine (norm_iteratedDeriv_ρ_succ_le ha hr n k hBq t).trans ?_
  have h1 : ∀ p ∈ Finset.range (n + 2), coef a (n + 1) p * B (p + k) ≤ δ := by
    intro p hp
    have hp' := Finset.mem_range.1 hp
    have hB' : B (p + k) = δ := by simp only [hB]; rw [if_pos (by omega)]
    rw [hB']
    have hδ0 : 0 ≤ δ := by positivity
    calc coef a (n + 1) p * δ ≤ 1 * δ :=
          mul_le_mul_of_nonneg_right ((coef_le_weight hε hg _ _).trans (weight_le_one M p)) hδ0
      _ = δ := one_mul δ
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hδ]
  have : ((n + 2 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) + 2 : ℝ) := by push_cast; linarith
  rw [mul_div_assoc']
  rw [div_le_iff₀ (by positivity)]
  have h2 : (0 : ℝ) ≤ (1 / 2) ^ (n + 1) := by positivity
  nlinarith

theorem exists_bound_iteratedDeriv_ρ (k j : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t, ‖iteratedDeriv k (ρ a (radii ε) j) t‖ ≤ C := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hc : HasCompactSupport (ρ a (radii ε) j) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_ρ_subset ha hr j)
  obtain ⟨C, hC⟩ := (hasCompactSupport_iteratedDeriv hc k).exists_bound_of_continuous
    ((contDiff_ρ ha hr j).continuous_iteratedDeriv k (by exact_mod_cast le_top))
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

def majorant (k j : ℕ) : ℝ :=
  (1 / 2) ^ j + if j ≤ k then (exists_bound_iteratedDeriv_ρ hε hg k j).choose else 0

theorem summable_majorant (k : ℕ) : Summable (majorant hε hg k) := by
  refine (summable_geometric_two).add (summable_of_ne_finset_zero (s := Finset.range (k + 1))
    fun j hj => ?_)
  rw [if_neg]; rw [Finset.mem_range] at hj; omega

theorem norm_iteratedDeriv_ρ_le_majorant (k j : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (ρ a (radii ε) j) t‖ ≤ majorant hε hg k j := by
  have hC := (exists_bound_iteratedDeriv_ρ hε hg k j).choose_spec
  unfold majorant
  split_ifs with hjk
  · linarith [hC.2 t, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j]
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    have := norm_iteratedDeriv_ρ_succ_le_half_pow hε hg n k (by omega) t
    linarith

def remSum (t : ℝ) : ℂ := ∑' j, ρ a (radii ε) j t

theorem contDiff_remSum : ContDiff ℝ ∞ (remSum (ε := ε) (a := a)) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  refine contDiff_tsum (fun j => contDiff_ρ ha hr j) (fun k _ => summable_majorant hε hg k)
    fun k j t _ => ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact norm_iteratedDeriv_ρ_le_majorant hε hg k j t

theorem summable_ρ (t : ℝ) : Summable fun j => ρ a (radii ε) j t :=
  Summable.of_norm_bounded (summable_majorant hε hg 0) fun j => by
    simpa using norm_iteratedDeriv_ρ_le_majorant hε hg 0 j t

theorem support_remSum_subset : support (remSum (ε := ε) (a := a)) ⊆ Icc 0 (ε / 2) := by
  intro t ht
  by_contra h
  apply ht
  unfold remSum
  refine (tsum_congr fun j => ?_).trans tsum_zero
  by_contra hj
  have h1 := support_ρ_subset (fun j => (hg j).1) (radii_pos hε) j hj
  exact h ⟨h1.1, h1.2.trans (Rs_radii_le hε j)⟩

theorem hasSum_integral_remSum {F : ℝ → ℂ} (hF : Continuous F) {B : ℝ}
    (hB : ∀ t ∈ Icc (-ε) ε, ‖F t‖ ≤ B) :
    HasSum (fun j => ∫ t, F t * ρ a (radii ε) j t) (∫ t, F t * remSum (ε := ε) (a := a) t) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hint : ∀ j, Integrable fun t => F t * ρ a (radii ε) j t := fun j =>
    (hF.mul (contDiff_ρ ha hr j).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_ρ_subset ha hr j)).mul_left
  have hbound : ∀ j, ∫ t, ‖F t * ρ a (radii ε) j t‖ ≤ (B * majorant hε hg 0 j) * (ε / 2) := by
    intro j
    refine integral_norm_le_of_support (hF.mul (contDiff_ρ ha hr j).continuous) (by positivity)
      ?_ ?_
    · intro t ht
      have h1 : t ∈ support (ρ a (radii ε) j) := fun h => ht (by simp [h])
      have h2 := support_ρ_subset ha hr j h1
      exact ⟨h2.1, h2.2.trans (Rs_radii_le hε j)⟩
    · intro t ht
      rw [Pi.mul_apply, norm_mul]
      have h1 := hB t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h2 : ‖ρ a (radii ε) j t‖ ≤ majorant hε hg 0 j := by
        simpa using norm_iteratedDeriv_ρ_le_majorant hε hg 0 j t
      exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hsum : Summable fun j => ∫ t, ‖F t * ρ a (radii ε) j t‖ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun t => norm_nonneg _) hbound
      (((summable_majorant hε hg 0).mul_left B).mul_right (ε / 2))
  have := hasSum_integral_of_summable_integral_norm hint hsum
  have e : ∫ t, F t * remSum (ε := ε) (a := a) t = ∫ t, ∑' j, F t * ρ a (radii ε) j t := by
    congr 1; funext t; rw [remSum, tsum_mul_left]
  rw [e]; exact this

end Sequence

theorem one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (m : ℕ) : (1 + x) ^ m ≤ 2 ^ m * (1 + x ^ m) := by
  have h1 : 1 + x ≤ 2 * max 1 x := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 x) ^ m ≤ 1 + x ^ m := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg hx m]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hx m]
  calc (1 + x) ^ m ≤ (2 * max 1 x) ^ m := pow_le_pow_left₀ (by linarith) h1 m
    _ = 2 ^ m * (max 1 x) ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (1 + x ^ m) := mul_le_mul_of_nonneg_left h2 (by positivity)

section Limit

variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg

theorem tendsto_fourier_Kc (ξ : ℝ) : ∃ l : ℂ,
    Tendsto (fun N => 𝓕 (fun t => (Kc a (radii ε) N t : ℂ)) ξ) atTop (𝓝 l) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hd : ∀ N, dist (𝓕 (KC a (radii ε) N) ξ) (𝓕 (KC a (radii ε) N.succ) ξ) ≤
      4 * π * |ξ| * (ε / 16) * (1 / 2) ^ N + (1 / 2) ^ (N + 1) := by
    intro N
    rw [dist_comm, dist_eq_norm]
    refine (norm_fourier_KC_succ_sub_le ha hr N ξ).trans (add_le_add (le_of_eq ?_) ?_)
    · unfold radii; rw [pow_add, pow_add, one_div_pow]; field_simp; ring
    · exact (hg (N + 1)).2.2.2
  have hs : Summable fun N : ℕ => 4 * π * |ξ| * (ε / 16) * (1 / 2 : ℝ) ^ N + (1 / 2) ^ (N + 1) :=
    (summable_geometric_two.mul_left _).add (summable_geometric_two.comp_injective
      (add_left_injective 1))
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable _ hd hs)

theorem decay_fourier_Kc (m : ℕ) : ∃ C N₀, ∀ N ≥ N₀, ∀ ξ : ℝ,
    ‖𝓕 (fun t => (Kc a (radii ε) N t : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ)) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  set P := ∏ j ∈ Finset.range m, (a j / π) with hP
  refine ⟨2 ^ m * (1 + P), m, fun N hN ξ => ?_⟩
  have h1 := abs_pow_mul_norm_fourier_KC_le ha hr N m (by omega) ξ
  have h2 := norm_fourier_KC_le_one ha hr N ξ
  have h3 := one_add_pow_le |ξ| (abs_nonneg ξ) m
  have hpos : 0 < (1 + |ξ|) ^ m := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  change ‖𝓕 (KC a (radii ε) N) ξ‖ * (1 + |ξ|) ^ m ≤ _
  calc ‖𝓕 (KC a (radii ε) N) ξ‖ * (1 + |ξ|) ^ m
      ≤ ‖𝓕 (KC a (radii ε) N) ξ‖ * (2 ^ m * (1 + |ξ| ^ m)) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = 2 ^ m * (‖𝓕 (KC a (radii ε) N) ξ‖ + |ξ| ^ m * ‖𝓕 (KC a (radii ε) N) ξ‖) := by ring
    _ ≤ 2 ^ m * (1 + P) := by gcongr

def climit (p : ℕ) : ℝ := ⨆ n, coef a n p

theorem bddAbove_coef (p : ℕ) : BddAbove (Set.range fun n => coef a n p) :=
  ⟨weight M p, by rintro _ ⟨n, rfl⟩; exact coef_le_weight hε hg n p⟩

theorem tendsto_coef (p : ℕ) : Tendsto (fun n => coef a n p) atTop (𝓝 (climit (a := a) p)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => coef_mono (fun j => (hg j).1) n p)
    (bddAbove_coef hε hg p)

theorem climit_le_weight (p : ℕ) : climit (a := a) p ≤ weight M p :=
  ciSup_le fun n => coef_le_weight hε hg n p

theorem climit_nonneg (p : ℕ) : 0 ≤ climit (a := a) p :=
  (coef_nonneg (fun j => (hg j).1) 0 p).trans (le_ciSup (bddAbove_coef hε hg p) 0)

end Limit

end LineKernel

open LineKernel in

theorem exists_dixmierMalliavin_line (M : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → ℝ) (g h : ℝ → ℂ), ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧
      tsupport g ⊆ Set.Icc (-ε) ε ∧ tsupport h ⊆ Set.Icc (-ε) ε ∧
      Summable (fun p => |c p| * M p) ∧
      ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → (∀ p, ∀ t ∈ Set.Icc (-ε) ε, ‖iteratedDeriv p F t‖ ≤ M p) →
        F 0 = (∑' p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t) + ∫ t, F t * h t := by
  choose a hg using fun j => (eventually_good M hε j).exists
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hKs : ∀ N, support (Kc a (radii ε) N) ⊆ Icc 0 (ε / 2) := fun N t ht =>
    ⟨(support_Kc_subset ha hr N ht).1, (support_Kc_subset ha hr N ht).2.trans (Rs_radii_le hε N)⟩
  obtain ⟨g, hgs, hgt, hgl⟩ := exists_smooth_weak_limit (K := Kc a (radii ε)) (a := 0)
    (b := ε / 2) (integrable_Kc ha hr) (Kc_nonneg ha hr) (integral_Kc_le_one ha hr) hKs
    (tendsto_fourier_Kc hε hg) (decay_fourier_Kc hε hg)
  have hsub : Icc 0 (ε / 2) ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) (by linarith)
  refine ⟨fun p => (-1) ^ p * climit (a := a) p, g, remSum (ε := ε) (a := a), hgs,
    contDiff_remSum hε hg, hgt.trans hsub,
    (closure_minimal (support_remSum_subset hε hg) isClosed_Icc).trans hsub, ?_, ?_⟩
  · refine Summable.of_norm_bounded
      (summable_geometric_two.mul_right (max 1 |M 0|)) fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (climit_nonneg hε hg p)]
    exact (mul_le_mul_of_nonneg_right (climit_le_weight hε hg p) (abs_nonneg _)).trans
      (weight_mul_abs_le M p)
  · intro F hF hFM

    have hA : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), ∫ t, F t * ρ a (radii ε) j t) atTop
        (𝓝 (∫ t, F t * remSum (ε := ε) (a := a) t)) :=
      ((hasSum_integral_remSum hε hg hF.continuous (fun t ht => by
        simpa using hFM 0 t ht)).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

    have hB : Tendsto (fun n => ∫ u, opT a (n + 1) F u * KC a (radii ε) n u) atTop
        (𝓝 (∑' p, (((-1) ^ p * climit (a := a) p : ℝ) : ℂ) *
          ∫ t, iteratedDeriv p F t * g t)) := by
      have hcont : ∀ p, Continuous (iteratedDeriv p F) := fun p =>
        hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
      have hKsC : ∀ n, support (KC a (radii ε) n) ⊆ Icc 0 (ε / 2) := fun n u hu =>
        hKs n (by simpa [KC] using hu)
      have hsplit : ∀ n, ∫ u, opT a (n + 1) F u * KC a (radii ε) n u =
          ∑' p, sc a (n + 1) p * ∫ u, iteratedDeriv p F u * KC a (radii ε) n u := by
        intro n
        rw [tsum_eq_sum (s := Finset.range (n + 2)) fun p hp => by
          rw [Finset.mem_range, not_lt] at hp
          simp [sc, coef_eq_zero a (by omega : n + 1 < p)]]
        simp only [opT, Finset.sum_mul]
        rw [integral_finsetSum (Finset.range (n + 1 + 1))
          (f := fun p u => sc a (n + 1) p * iteratedDeriv p F u * KC a (radii ε) n u)
          fun p _ => integrable_mul_of_support (φ := fun u => sc a (n + 1) p * iteratedDeriv p F u)
          (continuous_const.mul (hcont p)) (integrable_KC ha hr n) (hKsC n)]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← integral_const_mul]; congr 1; funext u; ring
      rw [show (fun n => ∫ u, opT a (n + 1) F u * KC a (radii ε) n u) =
          fun n => ∑' p, sc a (n + 1) p * ∫ u, iteratedDeriv p F u * KC a (radii ε) n u from
        funext hsplit]
      refine tendsto_tsum_of_dominated_convergence (bound := fun p => weight M p * |M p|) ?_ ?_ ?_
      · exact Summable.of_nonneg_of_le (fun p => mul_nonneg (weight_pos M p).le (abs_nonneg _))
          (weight_mul_abs_le M) (summable_geometric_two.mul_right _)
      · intro p
        have h1 : Tendsto (fun n => sc a (n + 1) p) atTop
            (𝓝 ((((-1) ^ p * climit (a := a) p : ℝ) : ℂ))) := by
          have := ((Complex.continuous_ofReal.tendsto _).comp
            ((tendsto_coef hε hg p).comp (tendsto_add_atTop_nat 1))).const_mul ((-1 : ℂ) ^ p)
          simpa [sc, Function.comp_def] using this
        exact h1.mul (hgl _ (hcont p))
      · refine Eventually.of_forall fun n p => ?_
        rw [norm_mul]
        have hsc : ‖sc a (n + 1) p‖ ≤ weight M p := by
          simp only [sc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (coef_nonneg ha _ _)]
          exact coef_le_weight hε hg _ _
        have hint : ‖∫ u, iteratedDeriv p F u * KC a (radii ε) n u‖ ≤ |M p| := by
          refine (norm_integral_le_integral_norm _).trans ?_
          calc ∫ u, ‖iteratedDeriv p F u * KC a (radii ε) n u‖
              ≤ ∫ u, |M p| * Kc a (radii ε) n u := by
                refine integral_mono (integrable_mul_of_support (hcont p) (integrable_KC ha hr n)
                  (hKsC n)).norm ((integrable_Kc ha hr n).const_mul _) fun u => ?_
                rw [norm_mul]
                simp only [KC, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (Kc_nonneg ha hr n u)]
                by_cases hu : Kc a (radii ε) n u = 0
                · simp [hu]
                · exact mul_le_mul_of_nonneg_right ((hFM p u (hsub (hKs n hu))).trans
                    (le_abs_self _)) (Kc_nonneg ha hr n u)
            _ = |M p| * ∫ u, Kc a (radii ε) n u := integral_const_mul _ _
            _ ≤ |M p| := by
                have := integral_Kc_le_one ha hr n
                have h0 : 0 ≤ |M p| := abs_nonneg _
                nlinarith
        exact mul_le_mul hsc hint (norm_nonneg _) (weight_pos M p).le
    have hlim := hB.add hA
    have hconst : (fun n => F 0) = fun n => (∫ u, opT a (n + 1) F u * KC a (radii ε) n u) +
        ∑ j ∈ Finset.range (n + 1), ∫ t, F t * ρ a (radii ε) j t :=
      funext fun n => stage_identity ha hr hF n
    rw [← hconst] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim

end

end GroundTheory.Automorphic
