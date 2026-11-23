import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.RobbaBounded
import GroundTheory.PAdicHodge.RobbaNewton
import GroundTheory.PAdicHodge.RobbaClosed
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

variable {a b : ℤ → K} {ρ : ℝ}

section Reflection

def rev (a : ℤ → K) : ℤ → K := fun n => a (-n)

@[simp] theorem rev_apply (a : ℤ → K) (n : ℤ) : rev a n = a (-n) := rfl

@[simp] theorem rev_rev (a : ℤ → K) : rev (rev a) = a := by funext n; simp

theorem rev_add (a b : ℤ → K) : rev (a + b) = rev a + rev b := rfl

theorem rev_cmul (a b : ℤ → K) : rev (cmul a b) = cmul (rev a) (rev b) := by
  funext n
  simp only [rev, cmul]
  rw [← (Equiv.neg ℤ).tsum_eq (fun i => a i * b (-n - i))]
  congr 1; funext i
  simp only [Equiv.neg_apply]
  congr 2; ring

theorem weight_rev (hρ : 0 < ρ) (n : ℤ) : ‖rev a n‖ * ρ⁻¹ ^ n = ‖a (-n)‖ * ρ ^ (-n) := by
  rw [rev_apply, inv_zpow']

theorem convergesAt_rev_iff (hρ : 0 < ρ) : ConvergesAt (rev a) ρ⁻¹ ↔ ConvergesAt a ρ := by
  have hinj : Function.Injective (fun n : ℤ => -n) := neg_injective
  constructor
  · intro h
    have := h.comp hinj.tendsto_cofinite
    refine this.congr fun n => ?_
    simp only [Function.comp, weight_rev hρ, neg_neg]
  · intro h
    have := h.comp hinj.tendsto_cofinite
    refine this.congr fun n => ?_
    simp only [Function.comp, weight_rev hρ]

theorem gaussNorm_rev (hρ : 0 < ρ) : gaussNorm (rev a) ρ⁻¹ = gaussNorm a ρ := by
  unfold gaussNorm
  simp_rw [weight_rev hρ]
  exact (Equiv.neg ℤ).iSup_comp (g := fun n => ‖a n‖ * ρ ^ n)

end Reflection

section FiniteSupport

theorem convergesAt_of_support {A B : ℤ} (hs : ∀ n, n < A ∨ B < n → a n = 0) (ρ : ℝ) :
    ConvergesAt a ρ := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(Set.finite_Icc A B).compl_mem_cofinite] with n hn
  simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hn
  rw [hs n (hn.imp id id), norm_zero, zero_mul]

theorem cmul_add_left_of_support {P : ℤ → K} {A B : ℤ} (hs : ∀ n, n < A ∨ B < n → P n = 0)
    (x y : ℤ → K) : cmul (x + y) P = cmul x P + cmul y P := by
  funext m
  simp only [cmul, Pi.add_apply, add_mul]
  have hfin : ∀ z : ℤ → K, Summable fun i => z i * P (m - i) := fun z =>
    summable_of_ne_finset_zero (s := Finset.Icc (m - B) (m - A)) fun i hi => by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hi
      rw [hs (m - i) (by omega), mul_zero]
  exact (hfin x).tsum_add (hfin y)

theorem cmul_eq_sum_of_support {P : ℤ → K} {A B : ℤ} (hs : ∀ n, n < A ∨ B < n → P n = 0)
    (x : ℤ → K) (m : ℤ) : cmul x P m = ∑ i ∈ Finset.Icc (m - B) (m - A), x i * P (m - i) := by
  unfold cmul
  refine tsum_eq_sum fun i hi => ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at hi
  rw [hs (m - i) (by omega), mul_zero]

end FiniteSupport

section Shift

def shift (x : ℤ → K) : ℤ → K := fun n => x (n - 1)

theorem cmul_shift (Q P : ℤ → K) : cmul (shift Q) P = shift (cmul Q P) := by
  funext n
  simp only [cmul, shift]
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq (fun i => Q (i - 1) * P (n - i))]
  congr 1; funext j
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  congr 2; ring

theorem shift_add (x y : ℤ → K) : shift (x + y) = shift x + shift y := rfl

theorem shift_single (k : ℤ) (c : K) : shift (Pi.single k c) = Pi.single (k + 1) c := by
  funext n
  simp only [shift, Pi.single_apply, sub_eq_iff_eq_add]

end Shift

end Laurent

namespace Laurent

theorem norm_add_mul_le_max (x y : K) {w : ℝ} (hw : 0 ≤ w) :
    ‖x + y‖ * w ≤ max (‖x‖ * w) (‖y‖ * w) := by
  rw [← max_mul_of_nonneg _ _ hw]
  exact mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) hw

theorem norm_sub_mul_le_max (x y : K) {w : ℝ} (hw : 0 ≤ w) :
    ‖x - y‖ * w ≤ max (‖x‖ * w) (‖y‖ * w) := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact norm_add_mul_le_max x (-y) hw

section Outer

def outDiv (P : ℤ → K) (H : ℤ) : ℕ → (ℤ → K) × (ℤ → K)
  | 0 => (Pi.single 0 (P H)⁻¹, Pi.single H 1 - (P H)⁻¹ • P)
  | k + 1 => (shift (outDiv P H k).1 + Pi.single 0 ((outDiv P H k).2 (H - 1) / P H),
      shift (outDiv P H k).2 - ((outDiv P H k).2 (H - 1) / P H) • P)

variable {P : ℤ → K} {L H : ℤ}

theorem outDiv_spec (hs : ∀ n, n < L ∨ H < n → P n = 0) (hPH : P H ≠ 0) (k : ℕ) :
    cmul (outDiv P H k).1 P + (outDiv P H k).2 = Pi.single (H + k) 1 := by
  induction k with
  | zero =>
    simp only [outDiv, cmul_single_left, Nat.cast_zero, add_zero]
    funext n
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_zero]
    ring
  | succ k ih =>
    simp only [outDiv]
    rw [cmul_add_left_of_support hs, cmul_shift, cmul_single_left]
    have h2 : shift (cmul (outDiv P H k).1 P) + shift (outDiv P H k).2 =
        Pi.single (H + ((k + 1 : ℕ) : ℤ)) 1 := by
      rw [← shift_add, ih, shift_single]; congr 1; push_cast; ring
    funext n
    have := congrFun h2 n
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_zero] at this ⊢
    linear_combination this

theorem outDiv_snd_support (hs : ∀ n, n < L ∨ H < n → P n = 0) (hPH : P H ≠ 0) (hLH : L ≤ H)
    (k : ℕ) : ∀ n, n < L ∨ H - 1 < n → (outDiv P H k).2 n = 0 := by
  induction k with
  | zero =>
    intro n hn
    simp only [outDiv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hnH : n = H
    · subst hnH; simp [hPH]
    · rw [Pi.single_eq_of_ne hnH, hs n (by omega), mul_zero, sub_zero]
  | succ k ih =>
    intro n hn
    simp only [outDiv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shift]
    by_cases hnH : n = H
    · subst hnH; field_simp; ring
    · rw [ih (n - 1) (by omega), hs n (by omega), mul_zero, sub_zero]

theorem outDiv_fst_support (k : ℕ) : ∀ n, n < 0 ∨ (k : ℤ) < n → (outDiv P H k).1 n = 0 := by
  induction k with
  | zero =>
    intro n hn
    simp only [outDiv]
    rw [Pi.single_eq_of_ne (by omega)]
  | succ k ih =>
    intro n hn
    simp only [outDiv, Pi.add_apply, shift]
    rw [ih (n - 1) (by push_cast at hn; omega), Pi.single_eq_of_ne (by push_cast at hn; omega),
      add_zero]

variable {τ : ℝ}

theorem outDiv_snd_weight (hτ : 0 < τ) (hPH : P H ≠ 0)
    (hout : ∀ i, ‖P i‖ * τ ^ i ≤ ‖P H‖ * τ ^ H) (k : ℕ) :
    ∀ j, ‖(outDiv P H k).2 j‖ * τ ^ j ≤ τ ^ (H + k) := by
  have hPH' : 0 < ‖P H‖ := norm_pos_iff.2 hPH
  induction k with
  | zero =>
    intro j
    simp only [outDiv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_zero, add_zero]
    by_cases hjH : j = H
    · subst hjH; simp [hPH]; positivity
    · rw [Pi.single_eq_of_ne hjH, zero_sub, norm_neg, norm_mul, norm_inv, mul_assoc,
        inv_mul_le_iff₀ hPH']
      exact hout j
  | succ k ih =>
    intro j
    simp only [outDiv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shift]
    have e : τ ^ (H + ((k + 1 : ℕ) : ℤ)) = τ ^ (H + k) * τ := by
      rw [← zpow_add_one₀ hτ.ne']; congr 1; push_cast; ring
    rw [e]
    refine (norm_sub_mul_le_max _ _ (by positivity)).trans (max_le ?_ ?_)
    · have := ih (j - 1)
      calc ‖(outDiv P H k).2 (j - 1)‖ * τ ^ j
          = ‖(outDiv P H k).2 (j - 1)‖ * τ ^ (j - 1) * τ := by
            rw [mul_assoc, ← zpow_add_one₀ hτ.ne', sub_add_cancel]
        _ ≤ τ ^ (H + k) * τ := mul_le_mul_of_nonneg_right this hτ.le
    · have h1 := ih (H - 1)
      rw [norm_mul, norm_div]
      calc ‖(outDiv P H k).2 (H - 1)‖ / ‖P H‖ * ‖P j‖ * τ ^ j
          = ‖(outDiv P H k).2 (H - 1)‖ / ‖P H‖ * (‖P j‖ * τ ^ j) := by ring
        _ ≤ ‖(outDiv P H k).2 (H - 1)‖ / ‖P H‖ * (‖P H‖ * τ ^ H) :=
            mul_le_mul_of_nonneg_left (hout j) (by positivity)
        _ = ‖(outDiv P H k).2 (H - 1)‖ * τ ^ (H - 1) * τ := by
            rw [show τ ^ H = τ ^ (H - 1) * τ by rw [← zpow_add_one₀ hτ.ne', sub_add_cancel]]
            field_simp
        _ ≤ τ ^ (H + k) * τ := mul_le_mul_of_nonneg_right h1 hτ.le

theorem outDiv_fst_weight (hτ : 0 < τ) (hPH : P H ≠ 0)
    (hout : ∀ i, ‖P i‖ * τ ^ i ≤ ‖P H‖ * τ ^ H) (k : ℕ) :
    ∀ j, ‖(outDiv P H k).1 j‖ * τ ^ j * (‖P H‖ * τ ^ H) ≤ τ ^ (H + k) := by
  have hPH' : 0 < ‖P H‖ := norm_pos_iff.2 hPH
  induction k with
  | zero =>
    intro j
    simp only [outDiv, Nat.cast_zero, add_zero]
    by_cases hj : j = 0
    · subst hj; simp only [Pi.single_eq_same, norm_inv, zpow_zero, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ hPH'.ne', one_mul]
    · rw [Pi.single_eq_of_ne hj, norm_zero, zero_mul, zero_mul]; positivity
  | succ k ih =>
    intro j
    simp only [outDiv, Pi.add_apply, shift]
    have e : τ ^ (H + ((k + 1 : ℕ) : ℤ)) = τ ^ (H + k) * τ := by
      rw [← zpow_add_one₀ hτ.ne']; congr 1; push_cast; ring
    rw [e, mul_assoc]
    refine (norm_add_mul_le_max _ _ (by positivity)).trans (max_le ?_ ?_)
    · have := ih (j - 1)
      calc ‖(outDiv P H k).1 (j - 1)‖ * (τ ^ j * (‖P H‖ * τ ^ H))
          = ‖(outDiv P H k).1 (j - 1)‖ * τ ^ (j - 1) * (‖P H‖ * τ ^ H) * τ := by
            rw [show τ ^ j = τ ^ (j - 1) * τ by rw [← zpow_add_one₀ hτ.ne', sub_add_cancel]]
            ring
        _ ≤ τ ^ (H + k) * τ := mul_le_mul_of_nonneg_right this hτ.le
    · by_cases hj : j = 0
      · subst hj
        simp only [Pi.single_eq_same, norm_div, zpow_zero, one_mul]
        have h1 := outDiv_snd_weight hτ hPH hout k (H - 1)
        calc ‖(outDiv P H k).2 (H - 1)‖ / ‖P H‖ * (‖P H‖ * τ ^ H)
            = ‖(outDiv P H k).2 (H - 1)‖ * τ ^ (H - 1) * τ := by
              rw [show τ ^ H = τ ^ (H - 1) * τ by rw [← zpow_add_one₀ hτ.ne', sub_add_cancel]]
              field_simp
          _ ≤ τ ^ (H + k) * τ := mul_le_mul_of_nonneg_right h1 hτ.le
      · rw [Pi.single_eq_of_ne hj, norm_zero, zero_mul]; positivity

end Outer

end Laurent

namespace Laurent

theorem tendsto_zero_of_eventually_le {ι : Type*} {l : Filter ι} {f : ι → ℝ}
    (h0 : ∀ x, 0 ≤ f x) (h : ∀ ε > 0, ∀ᶠ x in l, f x ≤ ε) : Tendsto f l (𝓝 0) :=
  tendsto_order.2 ⟨fun e he => Eventually.of_forall fun x => lt_of_lt_of_le he (h0 x),
    fun ε hε => (h (ε / 2) (half_pos hε)).mono fun x hx => hx.trans_lt (half_lt_self hε)⟩

section OuterSeries

variable {P : ℤ → K} {L H : ℤ} {τ : ℝ}

def outQuot (P : ℤ → K) (H : ℤ) (h : ℤ → K) : ℤ → K :=
  fun j => ∑' k : ℕ, h (H + k) * (outDiv P H k).1 j

def outRem (P : ℤ → K) (H : ℤ) (h : ℤ → K) : ℤ → K :=
  fun j => ∑' k : ℕ, h (H + k) * (outDiv P H k).2 j

variable {h : ℤ → K}

theorem tendsto_weight_shift (hh : ConvergesAt h τ) :
    Tendsto (fun k : ℕ => ‖h (H + k)‖ * τ ^ (H + (k : ℤ))) cofinite (𝓝 0) := by
  have hinj : Function.Injective (fun k : ℕ => H + (k : ℤ)) := fun a b e => by
    simpa using e
  exact hh.comp hinj.tendsto_cofinite

theorem norm_outDiv_fst_le (hτ : 0 < τ) (hPH : P H ≠ 0)
    (hout : ∀ i, ‖P i‖ * τ ^ i ≤ ‖P H‖ * τ ^ H) (k : ℕ) (j : ℤ) :
    ‖h (H + k) * (outDiv P H k).1 j‖ ≤
      ‖h (H + k)‖ * τ ^ (H + (k : ℤ)) / (τ ^ j * (‖P H‖ * τ ^ H)) := by
  have hPH' : 0 < ‖P H‖ := norm_pos_iff.2 hPH
  rw [norm_mul, le_div_iff₀ (by positivity), mul_assoc, ← mul_assoc ‖(outDiv P H k).1 j‖]
  exact mul_le_mul_of_nonneg_left (outDiv_fst_weight hτ hPH hout k j) (norm_nonneg _)

theorem norm_outDiv_snd_le (hτ : 0 < τ) (hPH : P H ≠ 0)
    (hout : ∀ i, ‖P i‖ * τ ^ i ≤ ‖P H‖ * τ ^ H) (k : ℕ) (j : ℤ) :
    ‖h (H + k) * (outDiv P H k).2 j‖ ≤ ‖h (H + k)‖ * τ ^ (H + (k : ℤ)) / τ ^ j := by
  rw [norm_mul, le_div_iff₀ (by positivity), mul_assoc]
  exact mul_le_mul_of_nonneg_left (outDiv_snd_weight hτ hPH hout k j) (norm_nonneg _)

theorem summable_outQuot_term (hτ : 0 < τ) (hPH : P H ≠ 0)
    (hout : ∀ i, ‖P i‖ * τ ^ i ≤ ‖P H‖ * τ ^ H) (hh : ConvergesAt h τ) (j : ℤ) :
    Summable fun k : ℕ => h (H + k) * (outDiv P H k).1 j := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := (tendsto_weight_shift (H := H) hh).div_const (τ ^ j * (‖P H‖ * τ ^ H))
  rw [zero_div] at this
  exact squeeze_zero (fun _ => norm_nonneg _) (norm_outDiv_fst_le hτ hPH hout · j) this

theorem summable_outRem_term (hτ : 0 < τ) (hPH : P H ≠ 0)
    (hout : ∀ i, ‖P i‖ * τ ^ i ≤ ‖P H‖ * τ ^ H) (hh : ConvergesAt h τ) (j : ℤ) :
    Summable fun k : ℕ => h (H + k) * (outDiv P H k).2 j := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := (tendsto_weight_shift (H := H) hh).div_const (τ ^ j)
  rw [zero_div] at this
  exact squeeze_zero (fun _ => norm_nonneg _) (norm_outDiv_snd_le hτ hPH hout · j) this

theorem outQuot_weight_le (hτ : 0 < τ) (hPH : P H ≠ 0)
    (hout : ∀ i, ‖P i‖ * τ ^ i ≤ ‖P H‖ * τ ^ H) (hh : ConvergesAt h τ) (j : ℤ) :
    ‖outQuot P H h j‖ * τ ^ j * (‖P H‖ * τ ^ H) ≤ gaussNorm h τ := by
  have hPH' : 0 < ‖P H‖ := norm_pos_iff.2 hPH
  have hc : 0 < τ ^ j * (‖P H‖ * τ ^ H) := by positivity
  rw [mul_assoc, ← le_div_iff₀ hc]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (div_nonneg (gaussNorm_nonneg hτ) hc.le) fun k => ?_
  exact (norm_outDiv_fst_le hτ hPH hout k j).trans
    (div_le_div_of_nonneg_right (hh.le_gaussNorm _) hc.le)

theorem outQuot_support (j : ℤ) (hj : j < 0) : outQuot P H h j = 0 := by
  unfold outQuot
  exact (tsum_congr fun k => by rw [outDiv_fst_support k j (Or.inl hj), mul_zero]).trans tsum_zero

theorem outRem_support (hs : ∀ n, n < L ∨ H < n → P n = 0) (hPH : P H ≠ 0) (hLH : L ≤ H)
    (j : ℤ) (hj : j < L ∨ H - 1 < j) : outRem P H h j = 0 := by
  unfold outRem
  exact (tsum_congr fun k => by rw [outDiv_snd_support hs hPH hLH k j hj, mul_zero]).trans tsum_zero

theorem convergesAt_outQuot (hτ : 0 < τ) (hPH : P H ≠ 0)
    (hout : ∀ i, ‖P i‖ * τ ^ i ≤ ‖P H‖ * τ ^ H) (hh : ConvergesAt h τ) :
    ConvergesAt (outQuot P H h) τ := by
  have hPH' : 0 < ‖P H‖ := norm_pos_iff.2 hPH
  set c := ‖P H‖ * τ ^ H with hc_def
  have hc : 0 < c := by positivity
  refine tendsto_zero_of_eventually_le (fun j => by positivity) fun ε hε => ?_
  obtain ⟨B, hB⟩ := (hh.finite_le (mul_pos hε hc)).bddAbove
  refine Filter.eventually_cofinite.2 ((Set.finite_Icc 0 (B - H)).subset fun j hj => ?_)
  simp only [Set.mem_setOf_eq, not_le] at hj
  simp only [Set.mem_Icc]
  by_contra hout'
  rcases lt_or_ge j 0 with hj0 | hj0
  · rw [outQuot_support j hj0, norm_zero, zero_mul] at hj; linarith
  have hjB : B - H < j := by omega
  have hbound : ‖outQuot P H h j‖ * τ ^ j * c ≤ ε * c := by
    rw [mul_assoc, ← le_div_iff₀ (by positivity)]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
    by_cases hk : (k : ℤ) < j
    · rw [outDiv_fst_support k j (Or.inr hk), mul_zero, norm_zero]; positivity
    · refine (norm_outDiv_fst_le hτ hPH hout k j).trans
        (div_le_div_of_nonneg_right ?_ (by positivity))
      by_contra hlt
      have := hB (show H + (k : ℤ) ∈ {n | ε * c ≤ ‖h n‖ * τ ^ n} from (not_le.1 hlt).le)
      omega
  have := le_of_mul_le_mul_right hbound hc
  linarith

theorem outDiv_series (hτ : 0 < τ) (hs : ∀ n, n < L ∨ H < n → P n = 0) (hPH : P H ≠ 0)
    (hout : ∀ i, ‖P i‖ * τ ^ i ≤ ‖P H‖ * τ ^ H) (hh : ConvergesAt h τ)
    (hsupp : ∀ n, n < H → h n = 0) : h = cmul (outQuot P H h) P + outRem P H h := by
  funext m
  have hQ := summable_outQuot_term hτ hPH hout hh
  have hR := summable_outRem_term hτ hPH hout hh
  have e1 : cmul (outQuot P H h) P m = ∑' k : ℕ, h (H + k) * cmul (outDiv P H k).1 P m := by
    rw [cmul_eq_sum_of_support hs]
    simp only [outQuot]
    simp_rw [← tsum_mul_right]
    rw [← Summable.tsum_finsetSum fun i _ => (hQ i).mul_right _]
    congr 1; funext k
    rw [cmul_eq_sum_of_support hs, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hspec : ∀ k : ℕ, cmul (outDiv P H k).1 P m =
      (Pi.single (H + (k : ℤ)) (1 : K) : ℤ → K) m - (outDiv P H k).2 m := fun k => by
    rw [← outDiv_spec hs hPH k]; simp
  have hsingle : ∑' k : ℕ, h (H + k) * (Pi.single (H + (k : ℤ)) (1 : K) : ℤ → K) m = h m := by
    rcases lt_or_ge m H with hm | hm
    · rw [hsupp m hm]
      refine (tsum_congr fun k => ?_).trans tsum_zero
      rw [Pi.single_eq_of_ne (by omega), mul_zero]
    · obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, m = H + k₀ := ⟨(m - H).toNat, by omega⟩
      rw [tsum_eq_single k₀ fun k hk => by
        rw [Pi.single_eq_of_ne (by omega), mul_zero], hk₀, Pi.single_eq_same, mul_one]
  have hsumS : Summable fun k : ℕ => h (H + k) * (Pi.single (H + (k : ℤ)) (1 : K) : ℤ → K) m :=
    summable_of_ne_finset_zero (s := {(m - H).toNat}) fun k hk => by
      simp only [Finset.mem_singleton] at hk
      rw [Pi.single_eq_of_ne (by omega), mul_zero]
  rw [Pi.add_apply, e1]
  simp_rw [hspec, mul_sub]
  rw [hsumS.tsum_sub (hR m), hsingle]
  simp [outRem]

end OuterSeries

section Division

variable {P : ℤ → K} {L H : ℤ} {τ : ℝ}

theorem gaussNorm_eq_of_dominant (hs : ∀ n, n < L ∨ H < n → P n = 0) {N : ℤ}
    (hdom : ∀ i, ‖P i‖ * τ ^ i ≤ ‖P N‖ * τ ^ N) : gaussNorm P τ = ‖P N‖ * τ ^ N :=
  le_antisymm (gaussNorm_le hdom) ((convergesAt_of_support hs τ).le_gaussNorm N)

theorem rev_support (hs : ∀ n, n < L ∨ H < n → P n = 0) :
    ∀ n, n < -H ∨ -L < n → rev P n = 0 := fun n hn => hs (-n) (by omega)

theorem rev_dominant (hτ : 0 < τ) {N : ℤ} (hdom : ∀ i, ‖P i‖ * τ ^ i ≤ ‖P N‖ * τ ^ N) :
    ∀ i, ‖rev P i‖ * τ⁻¹ ^ i ≤ ‖rev P (-N)‖ * τ⁻¹ ^ (-N) := fun i => by
  rw [weight_rev hτ, weight_rev hτ, neg_neg]; exact hdom (-i)

theorem weierstrass_division {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) (hLH : L ≤ H)
    (hs : ∀ n, n < L ∨ H < n → P n = 0) (hPL : P L ≠ 0) (hPH : P H ≠ 0)
    (hin : ∀ i, ‖P i‖ * τ₁ ^ i ≤ ‖P L‖ * τ₁ ^ L) (hout : ∀ i, ‖P i‖ * τ₂ ^ i ≤ ‖P H‖ * τ₂ ^ H)
    {h : ℤ → K} (h₁ : ConvergesAt h τ₁) (h₂ : ConvergesAt h τ₂) :
    ∃ q r : ℤ → K, ConvergesAt q τ₁ ∧ ConvergesAt q τ₂ ∧ (∀ n, n < L ∨ H < n → r n = 0) ∧
      h = cmul q P + r ∧
      gaussNorm q τ₁ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) ∧
      gaussNorm q τ₂ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) ∧
      gaussNorm r τ₁ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) *
        gaussNorm P τ₁ ∧
      gaussNorm r τ₂ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) *
        gaussNorm P τ₂ := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  have hPL' : 0 < ‖P L‖ := norm_pos_iff.2 hPL
  have hPH' : 0 < ‖P H‖ := norm_pos_iff.2 hPH
  have hG₁ : gaussNorm P τ₁ = ‖P L‖ * τ₁ ^ L := gaussNorm_eq_of_dominant hs hin
  have hG₂ : gaussNorm P τ₂ = ‖P H‖ * τ₂ ^ H := gaussNorm_eq_of_dominant hs hout
  have hG₁p : 0 < gaussNorm P τ₁ := by rw [hG₁]; positivity
  have hG₂p : 0 < gaussNorm P τ₂ := by rw [hG₂]; positivity
  set M := max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂)

  set hp := trunc h (Set.Ici H)
  set hm := trunc h (Set.Iio L)
  set h0 := trunc h (Set.Ico L H)
  have hsplit : h = hp + hm + h0 := by
    funext n
    simp only [hp, hm, h0, trunc, Pi.add_apply, Set.indicator_apply, Set.mem_Ici, Set.mem_Iio,
      Set.mem_Ico]
    split_ifs <;> first | (exfalso; omega) | simp

  have hp₂ : ConvergesAt hp τ₂ := h₂.trunc hτ₂ _
  set qp := outQuot P H hp
  set rp := outRem P H hp
  have ep : hp = cmul qp P + rp := outDiv_series hτ₂ hs hPH hout hp₂ fun n hn => by
    simp [hp, trunc, Set.indicator_apply, not_le.2 hn]
  have qp₂ : ConvergesAt qp τ₂ := convergesAt_outQuot hτ₂ hPH hout hp₂
  have qp_supp : ∀ n, n < 0 → qp n = 0 := fun n hn => outQuot_support n hn
  have qp₁ : ConvergesAt qp τ₁ := qp₂.of_support_ge qp_supp hτ₁ hτ
  have gqp₂ : gaussNorm qp τ₂ ≤ gaussNorm h τ₂ / gaussNorm P τ₂ := by
    rw [hG₂]
    refine gaussNorm_le fun j => ?_
    rw [le_div_iff₀ (by positivity)]
    exact (outQuot_weight_le hτ₂ hPH hout hp₂ j).trans (gaussNorm_trunc_le hτ₂ h₂ _)
  have gqp₁ : gaussNorm qp τ₁ ≤ gaussNorm qp τ₂ := by
    simpa using gaussNorm_le_of_support_ge qp_supp qp₂ hτ₁ hτ

  have hτ₁i : 0 < τ₁⁻¹ := inv_pos.2 hτ₁
  have hrevP := rev_support hs
  have hrevPL : rev P (-L) ≠ 0 := by simpa using hPL
  have hrevdom := rev_dominant hτ₁ hin
  have hm₁ : ConvergesAt hm τ₁ := h₁.trunc hτ₁ _
  have hrm : ConvergesAt (rev hm) τ₁⁻¹ := (convergesAt_rev_iff hτ₁).2 hm₁
  set x := outQuot (rev P) (-L) (rev hm)
  set y := outRem (rev P) (-L) (rev hm)
  have ex : rev hm = cmul x (rev P) + y := outDiv_series hτ₁i hrevP hrevPL hrevdom hrm
    fun n hn => by simp [hm, trunc, Set.indicator_apply, show ¬ (-n < L) by omega]
  set qm := rev x
  set rm := rev y
  have em : hm = cmul qm P + rm := by
    have := congrArg rev ex
    rw [rev_rev, rev_add, rev_cmul, rev_rev] at this
    exact this
  have x₁ : ConvergesAt x τ₁⁻¹ := convergesAt_outQuot hτ₁i hrevPL hrevdom hrm
  have qm₁ : ConvergesAt qm τ₁ := by
    have := (convergesAt_rev_iff hτ₁i).2 x₁
    rwa [inv_inv] at this
  have qm_supp : ∀ n, 0 < n → qm n = 0 := fun n hn => outQuot_support (-n) (by omega)
  have qm₂ : ConvergesAt qm τ₂ := qm₁.of_support_le qm_supp hτ₁ hτ
  have gqm₁ : gaussNorm qm τ₁ ≤ gaussNorm h τ₁ / gaussNorm P τ₁ := by
    have e : gaussNorm qm τ₁ = gaussNorm x τ₁⁻¹ := by
      have := gaussNorm_rev (a := x) hτ₁i
      rwa [inv_inv] at this
    rw [e, hG₁]
    refine gaussNorm_le fun j => ?_
    rw [le_div_iff₀ (by positivity)]
    have w := outQuot_weight_le hτ₁i hrevPL hrevdom hrm j
    rw [gaussNorm_rev hτ₁] at w
    have e2 : ‖rev P (-L)‖ * τ₁⁻¹ ^ (-L) = ‖P L‖ * τ₁ ^ L := by
      rw [weight_rev hτ₁, neg_neg]
    rw [e2] at w
    exact w.trans (gaussNorm_trunc_le hτ₁ h₁ _)
  have gqm₂ : gaussNorm qm τ₂ ≤ gaussNorm qm τ₁ := by
    simpa using gaussNorm_le_of_support_le qm_supp qm₁ hτ₁ hτ

  set q := qp + qm
  set r := rp + rm + h0
  have hq₁ : ConvergesAt q τ₁ := qp₁.add hτ₁ qm₁
  have hq₂ : ConvergesAt q τ₂ := qp₂.add hτ₂ qm₂
  have eq : h = cmul q P + r := by
    simp only [q, r]
    rw [cmul_add_left_of_support hs]
    conv_lhs => rw [hsplit, ep, em]
    abel
  have hM1 : gaussNorm h τ₁ / gaussNorm P τ₁ ≤ M := le_max_left _ _
  have hM2 : gaussNorm h τ₂ / gaussNorm P τ₂ ≤ M := le_max_right _ _
  have gq₁ : gaussNorm q τ₁ ≤ M :=
    (gaussNorm_add_le hτ₁ qp₁ qm₁).trans (max_le ((gqp₁.trans gqp₂).trans hM2) (gqm₁.trans hM1))
  have gq₂ : gaussNorm q τ₂ ≤ M :=
    (gaussNorm_add_le hτ₂ qp₂ qm₂).trans (max_le (gqp₂.trans hM2) ((gqm₂.trans gqm₁).trans hM1))
  have hr : r = h - cmul q P := by rw [eq]; abel
  have hP₁ : ConvergesAt P τ₁ := convergesAt_of_support hs τ₁
  have hP₂ : ConvergesAt P τ₂ := convergesAt_of_support hs τ₂
  have gr : ∀ τ, 0 < τ → ConvergesAt h τ → ConvergesAt q τ → ConvergesAt P τ → 0 < gaussNorm P τ →
      gaussNorm h τ / gaussNorm P τ ≤ M → gaussNorm q τ ≤ M → gaussNorm r τ ≤ M * gaussNorm P τ := by
    intro τ hτ0 hhτ hqτ hPτ hGp hb1 hb2
    rw [hr]
    refine (gaussNorm_sub_le hτ0 hhτ (hqτ.cmul hτ0 hPτ)).trans (max_le ?_ ?_)
    · rwa [div_le_iff₀ hGp] at hb1
    · exact (gaussNorm_cmul_le hτ0 hqτ hPτ).trans
        (mul_le_mul_of_nonneg_right hb2 (gaussNorm_nonneg hτ0))
  refine ⟨q, r, hq₁, hq₂, fun n hn => ?_, eq, gq₁, gq₂,
    gr τ₁ hτ₁ h₁ hq₁ hP₁ hG₁p hM1 gq₁, gr τ₂ hτ₂ h₂ hq₂ hP₂ hG₂p hM2 gq₂⟩
  simp only [r, Pi.add_apply]
  have h1 : rp n = 0 := outRem_support hs hPH hLH n (by omega)
  have h2 : rm n = 0 := outRem_support hrevP hrevPL (by omega) (-n) (by omega)
  rw [h1, h2]
  simp [h0, trunc, Set.indicator_apply]
  omega

end Division

end Laurent

end GroundTheory.PAdicHodge
