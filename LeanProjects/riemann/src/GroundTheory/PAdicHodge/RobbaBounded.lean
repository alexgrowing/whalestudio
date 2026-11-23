import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.PerfectoidField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

variable {a b u : ℤ → K} {ρ : ℝ}

theorem gaussNorm_cmul_le (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    gaussNorm (cmul a b) ρ ≤ gaussNorm a ρ * gaussNorm b ρ :=
  gaussNorm_le fun n => norm_cmul_mul_zpow_le hρ
    (mul_nonneg (gaussNorm_nonneg hρ) (gaussNorm_nonneg hρ)) fun i =>
      mul_le_mul (ha.le_gaussNorm i) (hb.le_gaussNorm _) (by positivity) (gaussNorm_nonneg hρ)

def cpow (u : ℤ → K) : ℕ → ℤ → K
  | 0 => Pi.single 0 1
  | k + 1 => cmul u (cpow u k)

theorem ConvergesAt.cpow (hρ : 0 < ρ) (hu : ConvergesAt u ρ) : ∀ k, ConvergesAt (cpow u k) ρ
  | 0 => convergesAt_single 0 1 ρ
  | k + 1 => hu.cmul hρ (hu.cpow hρ k)

theorem gaussNorm_cpow_le (hρ : 0 < ρ) (hu : ConvergesAt u ρ) :
    ∀ k, gaussNorm (cpow u k) ρ ≤ gaussNorm u ρ ^ k
  | 0 => by simp [cpow, gaussNorm_single_zero_one hρ]
  | k + 1 => by
    rw [pow_succ']
    exact (gaussNorm_cmul_le hρ hu (hu.cpow hρ k)).trans
      (mul_le_mul_of_nonneg_left (gaussNorm_cpow_le hρ hu k) (gaussNorm_nonneg hρ))

theorem weight_cpow_le (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (k : ℕ) (n : ℤ) :
    ‖cpow u k n‖ * ρ ^ n ≤ gaussNorm u ρ ^ k :=
  ((hu.cpow hρ k).le_gaussNorm n).trans (gaussNorm_cpow_le hρ hu k)

def geomInv (u : ℤ → K) : ℤ → K := fun n => ∑' k : ℕ, (-1) ^ k * cpow u k n

theorem norm_geom_term_le (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (k : ℕ) (n : ℤ) :
    ‖(-1) ^ k * cpow u k n‖ ≤ gaussNorm u ρ ^ k / ρ ^ n := by
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, le_div_iff₀ (zpow_pos hρ n)]
  exact weight_cpow_le hρ hu k n

theorem tendsto_geom_term (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (hq : gaussNorm u ρ < 1) (n : ℤ) :
    Tendsto (fun k : ℕ => (-1) ^ k * cpow u k n) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Nat.cofinite_eq_atTop]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (gaussNorm_nonneg hρ) hq).div_const (ρ ^ n)
  rw [zero_div] at h
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => norm_geom_term_le hρ hu k n) h

theorem ConvergesAt.geomInv (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (hq : gaussNorm u ρ < 1) :
    ConvergesAt (geomInv u) ρ := by
  refine tendsto_order.2 ⟨fun x hx => Eventually.of_forall fun n =>
    lt_of_lt_of_le hx (by positivity), fun ε hε => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (half_pos hε) hq
  have hS : (⋃ k ∈ Finset.range k₀, {n : ℤ | ε / 2 ≤ ‖Laurent.cpow u k n‖ * ρ ^ n}).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun k _ => (hu.cpow hρ k).finite_le (half_pos hε)
  refine Filter.eventually_cofinite.2 (hS.subset fun n hn => ?_)
  simp only [Set.mem_setOf_eq, not_lt] at hn
  by_contra hcon
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, not_exists, not_and, not_le]
    at hcon
  have hρn : 0 < ρ ^ n := zpow_pos hρ n
  have : ‖Laurent.geomInv u n‖ * ρ ^ n ≤ ε / 2 := by
    rw [← le_div_iff₀ hρn]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, le_div_iff₀ hρn]
    rcases lt_or_ge k k₀ with hk | hk
    · exact (hcon k hk).le
    · exact (weight_cpow_le hρ hu k n).trans ((pow_le_pow_of_le_one (gaussNorm_nonneg hρ)
        hq.le hk).trans hk₀.le)
  linarith

theorem cmul_one_add_geomInv (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (hq : gaussNorm u ρ < 1) :
    cmul (Pi.single 0 1 + u) (geomInv u) = Pi.single 0 1 := by
  have hw := hu.geomInv hρ hq
  rw [add_cmul hρ (convergesAt_single 0 1 ρ) hu hw, single_zero_one_cmul]
  funext n
  have hsum : Summable (Function.uncurry fun i (k : ℕ) => u i * ((-1) ^ k * cpow u k (n - i))) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hq' : Tendsto (fun k : ℕ => gaussNorm u ρ ^ k) cofinite (𝓝 0) := by
      rw [Nat.cofinite_eq_atTop]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (gaussNorm_nonneg hρ) hq
    have h := (tendsto_mul_cofinite_nhds_zero hu hq').div_const (ρ ^ n)
    rw [zero_div] at h
    refine squeeze_zero (fun _ => norm_nonneg _) (fun ⟨i, k⟩ => ?_) h
    simp only [Function.uncurry_apply_pair, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
    have hρn : 0 < ρ ^ n := zpow_pos hρ n
    rw [le_div_iff₀ hρn]
    have e : ρ ^ n = ρ ^ i * ρ ^ (n - i) := by rw [← zpow_add₀ hρ.ne']; congr 1; ring
    rw [e]
    have h1 := weight_cpow_le hρ hu k (n - i)
    calc ‖u i‖ * ‖cpow u k (n - i)‖ * (ρ ^ i * ρ ^ (n - i))
        = (‖u i‖ * ρ ^ i) * (‖cpow u k (n - i)‖ * ρ ^ (n - i)) := by ring
      _ ≤ (‖u i‖ * ρ ^ i) * gaussNorm u ρ ^ k :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
  have e1 : cmul u (geomInv u) n = ∑' k : ℕ, (-1) ^ k * cpow u (k + 1) n := by
    simp only [cmul, geomInv, cpow]
    simp_rw [← tsum_mul_left]
    rw [← hsum.tsum_comm]
    congr 1; funext k
    congr 1; funext i; ring
  have e2 : geomInv u n = (Pi.single 0 (1 : K) : ℤ → K) n - ∑' k : ℕ, (-1) ^ k * cpow u (k + 1) n := by
    unfold geomInv
    rw [NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (tendsto_geom_term hρ hu hq n) |>.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, cpow, pow_succ, mul_neg, mul_one, neg_mul, tsum_neg]
    ring
  rw [Pi.add_apply, e1, e2, Pi.single_apply]
  ring

end Laurent

namespace Robba

instance : Nontrivial (Robba K) :=
  ⟨⟨0, 1, fun h => by simpa using congrFun (congrArg Robba.coeff h) 0⟩⟩

theorem isUnit_one_add {U : Robba K} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hU : ∀ ρ, s ≤ ρ → ρ < 1 → ConvergesAt U.coeff ρ ∧ gaussNorm U.coeff ρ < 1) :
    IsUnit (1 + U) := by
  let W : Robba K := ⟨geomInv U.coeff, ⟨s, hs1, fun ρ h1 h2 h3 =>
    (hU ρ h1 h2).1.geomInv h3 (hU ρ h1 h2).2⟩⟩
  have h : (1 + U) * W = 1 :=
    Robba.ext (cmul_one_add_geomInv hs0 (hU s le_rfl hs1).1 (hU s le_rfl hs1).2)
  exact ⟨⟨_, W, h, by rw [mul_comm]; exact h⟩, rfl⟩

end Robba

theorem exists_norm_le_mul_of_lt [IsDiscreteValuationRing (normInteger K)] :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ x y : K, ‖y‖ < ‖x‖ → ‖y‖ ≤ q * ‖x‖ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (normInteger K)
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hunit : ∀ z : normInteger K, IsUnit z ↔ ‖(z : K)‖ = 1 := by
    intro z
    rw [normInteger_integers.isUnit_iff_valuation_eq_one, NormedField.valuation_apply,
      ← NNReal.coe_eq_one]
    rfl
  have hϖ1 : ‖(ϖ : K)‖ < 1 :=
    lt_of_le_of_ne (mem_normInteger.1 ϖ.2) fun h => hϖ.not_isUnit ((hunit ϖ).2 h)
  refine ⟨‖(ϖ : K)‖, norm_nonneg _, hϖ1, fun x y hxy => ?_⟩
  have hx : x ≠ 0 := by
    rintro rfl
    simp only [norm_zero] at hxy
    exact absurd hxy (not_lt.2 (norm_nonneg _))
  have hz : ‖y / x‖ < 1 := by rw [norm_div, div_lt_one (norm_pos_iff.2 hx)]; exact hxy
  let z : normInteger K := ⟨y / x, mem_normInteger.2 hz.le⟩
  have hzmem : z ∈ IsLocalRing.maximalIdeal (normInteger K) :=
    (IsLocalRing.mem_maximalIdeal z).2 (mem_nonunits_iff.2 fun hu => hz.ne ((hunit z).1 hu))
  rw [hmax, Ideal.mem_span_singleton'] at hzmem
  obtain ⟨t, ht⟩ := hzmem
  have e : y / x = (t : K) * (ϖ : K) := (congrArg Subtype.val ht).symm
  have ht1 : ‖(t : K)‖ ≤ 1 := mem_normInteger.1 t.2
  have : ‖y‖ = ‖y / x‖ * ‖x‖ := by rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hx)]
  rw [this, e, norm_mul]
  calc ‖(t : K)‖ * ‖(ϖ : K)‖ * ‖x‖ = ‖(t : K)‖ * (‖(ϖ : K)‖ * ‖x‖) := by ring
    _ ≤ 1 * (‖(ϖ : K)‖ * ‖x‖) := mul_le_mul_of_nonneg_right ht1 (by positivity)
    _ = ‖(ϖ : K)‖ * ‖x‖ := one_mul _

namespace Robba

variable [IsDiscreteValuationRing (normInteger K)]

theorem isUnit_of_mem_bounded {f : Robba K} (hf : f ∈ bounded K) (h0 : f ≠ 0) : IsUnit f := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_norm_le_mul_of_lt (K := K)
  set a := f.coeff with ha_def
  have ha0 : a ≠ 0 := fun h => h0 (Robba.ext h)
  obtain ⟨n₀, hn₀⟩ := Function.ne_iff.1 ha0
  have hbdd : BddAbove (Set.range fun n => ‖a n‖) := hf
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f f

  obtain ⟨N, hN⟩ : ∃ N, ∀ n, ‖a n‖ ≤ ‖a N‖ := by
    have hMpos : 0 < ⨆ n, ‖a n‖ := lt_of_lt_of_le (norm_pos_iff.2 hn₀) (le_ciSup hbdd n₀)
    have hlt : q * ⨆ n, ‖a n‖ < ⨆ n, ‖a n‖ := by nlinarith
    obtain ⟨n₁, hn₁⟩ := exists_lt_of_lt_ciSup hlt
    refine ⟨n₁, fun n => not_lt.1 fun hn => ?_⟩
    have := hq _ _ hn
    have := le_ciSup hbdd n
    nlinarith
  set M := ‖a N‖
  have hM : 0 < M := lt_of_lt_of_le (norm_pos_iff.2 hn₀) (hN n₀)

  set S := {n | ‖a n‖ = M}
  have hF := (hc r le_rfl hr1).1.finite_le hM
  obtain ⟨B, hB⟩ := hF.bddBelow
  have hSbdd : BddBelow S := ⟨min B 0, fun n hn => by
    rcases le_or_gt n 0 with h | h
    · refine min_le_of_left_le (hB ?_)
      simp only [Set.mem_setOf_eq]
      have : (1 : ℝ) ≤ r ^ n := one_le_zpow_of_nonpos₀ hr0 hr1.le h
      have hn : ‖a n‖ = M := hn
      nlinarith
    · exact (min_le_right _ _).trans h.le⟩
  set m := sInf S
  have hmS : ‖a m‖ = M := Int.csInf_mem (s := S) ⟨N, rfl⟩ hSbdd
  have hbelow : ∀ n < m, ‖a n‖ < M := fun n hn =>
    lt_of_le_of_ne (hN n) fun h => absurd (csInf_le hSbdd h) (not_le.2 hn)
  have ham : a m ≠ 0 := fun h => by rw [h, norm_zero] at hmS; linarith

  have hMr : 0 < M * r ^ m := by positivity
  have hG := (hc r le_rfl hr1).1.finite_le hMr
  obtain ⟨B', hB'⟩ := hG.bddBelow
  set D := (m - B').toNat
  obtain ⟨ρ₀, hρ₀r, hρ₀1, hρ₀q⟩ : ∃ ρ₀, r ≤ ρ₀ ∧ ρ₀ < 1 ∧ q < ρ₀ ^ D := by
    have hlim : Tendsto (fun ρ : ℝ => ρ ^ D) (𝓝[<] 1) (𝓝 1) := by
      simpa using ((continuous_pow D).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    have hI : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Set.Ioo r 1 := Ioo_mem_nhdsLT hr1
    obtain ⟨ρ, hρ1, hρ2⟩ := (hI.and (hlim.eventually (lt_mem_nhds hq1))).exists
    exact ⟨ρ, hρ1.1.le, hρ1.2, hρ2⟩
  have dom : ∀ ρ, ρ₀ ≤ ρ → ρ < 1 → ∀ k, k ≠ m → ‖a k‖ * ρ ^ k < M * ρ ^ m := by
    intro ρ h1 h2 k hk
    have hρ : 0 < ρ := hr0.trans_le (hρ₀r.trans h1)
    rcases lt_or_gt_of_ne hk with hk | hk
    · have hρk : 0 < ρ ^ k := zpow_pos hρ k
      have e : ρ ^ m = ρ ^ (m - k) * ρ ^ k := by rw [← zpow_add₀ hρ.ne']; congr 1; ring
      rw [e, ← mul_assoc]
      refine mul_lt_mul_of_pos_right ?_ hρk
      by_cases hkG : M * r ^ m ≤ ‖a k‖ * r ^ k
      · have hkB : B' ≤ k := hB' hkG
        have h3 : ρ ^ (D : ℤ) ≤ ρ ^ (m - k) :=
          zpow_le_zpow_right_of_le_one₀ hρ h2.le (by omega)
        have h4 : ρ₀ ^ D ≤ ρ ^ D := pow_le_pow_left₀ (hr0.le.trans hρ₀r) h1 D
        rw [zpow_natCast] at h3
        have h5 : ‖a k‖ ≤ q * M := by rw [← hmS]; exact hq _ _ (by rw [hmS]; exact hbelow k hk)
        nlinarith
      · have hrk : 0 < r ^ k := zpow_pos hr0 k
        have e' : r ^ m = r ^ (m - k) * r ^ k := by rw [← zpow_add₀ hr0.ne']; congr 1; ring
        rw [not_le, e', ← mul_assoc] at hkG
        have h6 : ‖a k‖ < M * r ^ (m - k) := lt_of_mul_lt_mul_right hkG hrk.le
        have h7 : r ^ (m - k) ≤ ρ ^ (m - k) :=
          zpow_le_zpow_left₀ (by omega) hr0.le (hρ₀r.trans h1)
        nlinarith
    · calc ‖a k‖ * ρ ^ k ≤ M * ρ ^ k := mul_le_mul_of_nonneg_right (hN k) (by positivity)
        _ < M * ρ ^ m := mul_lt_mul_of_pos_left (zpow_lt_zpow_right_of_lt_one₀ hρ h2 hk) hM

  set u : ℤ → K := fun n => if n = 0 then 0 else a (n + m) / a m
  have hweight : ∀ ρ, 0 < ρ → ∀ n, n ≠ 0 →
      ‖u n‖ * ρ ^ n = ‖a (n + m)‖ * ρ ^ (n + m) / (M * ρ ^ m) := by
    intro ρ hρ n hn
    simp only [u, if_neg hn, norm_div, hmS]
    rw [zpow_add₀ hρ.ne']
    field_simp
  have hu : ∀ ρ, ρ₀ ≤ ρ → ρ < 1 → ConvergesAt u ρ ∧ gaussNorm u ρ < 1 := by
    intro ρ h1 h2
    have hρ : 0 < ρ := hr0.trans_le (hρ₀r.trans h1)
    have ha : ConvergesAt a ρ := (hc ρ (hρ₀r.trans h1) h2).1
    have hshift : Tendsto (fun n : ℤ => ‖a (n + m)‖ * ρ ^ (n + m) / (M * ρ ^ m)) cofinite
        (𝓝 0) := by
      have := (ha.comp (add_left_injective m).tendsto_cofinite).div_const (M * ρ ^ m)
      simpa [Function.comp] using this
    have hconv : ConvergesAt u ρ := by
      refine squeeze_zero (fun n => by positivity) (fun n => ?_) hshift
      by_cases hn : n = 0
      · simp only [u, if_pos hn, norm_zero, zero_mul]; positivity
      · exact (hweight ρ hρ n hn).le
    refine ⟨hconv, ?_⟩
    by_cases hu0 : u = 0
    · rw [hu0]
      have : gaussNorm (0 : ℤ → K) ρ = 0 := by simp [gaussNorm]
      rw [this]; exact one_pos
    obtain ⟨n, hn⟩ := hconv.exists_eq_gaussNorm hρ hu0
    rw [← hn]
    by_cases hn0 : n = 0
    · simp only [u, if_pos hn0, norm_zero, zero_mul]; exact one_pos
    · rw [hweight ρ hρ n hn0, div_lt_one (by positivity)]
      exact dom ρ h1 h2 (n + m) (by omega)
  set U : Robba K := ⟨u, ⟨ρ₀, hρ₀1, fun ρ h1 h2 _ => (hu ρ h1 h2).1⟩⟩
  have hfU : f = single m (a m) * (1 + U) := by
    ext n
    rw [coeff_single_mul]
    show a n = a m * ((Pi.single 0 (1 : K) : ℤ → K) (n - m) + u (n - m))
    by_cases hn : n - m = 0
    · have : n = m := by omega
      subst this; simp [u]
    · simp only [u, Pi.single_apply, if_neg hn, zero_add, sub_add_cancel]
      field_simp
  rw [hfU]
  exact (isUnit_single m ham).mul (isUnit_one_add (hr0.trans_le hρ₀r) hρ₀1 hu)

theorem isField_bounded : IsField (bounded K) where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    have hx' : (x : Robba K) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨hf, u, hu⟩ := isUnit_iff_isUnit_bounded.1 (isUnit_of_mem_bounded x.2 hx')
    refine ⟨↑u⁻¹, ?_⟩
    have : (⟨(x : Robba K), hf⟩ : bounded K) = x := rfl
    rw [← this, ← hu]
    exact u.mul_inv

theorem isUnit_iff_mem_bounded {f : Robba K} : IsUnit f ↔ f ∈ bounded K ∧ f ≠ 0 := by
  refine ⟨fun h => ?_, fun h => isUnit_of_mem_bounded h.1 h.2⟩
  obtain ⟨g, rfl⟩ := isUnit_iff.1 h
  exact ⟨(g : bounded K).2, h.ne_zero⟩

end Robba

end GroundTheory.PAdicHodge
