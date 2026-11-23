import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.ChiPSt

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Filter Topology Asymptotics

def hsDefect (D : ℕ) (chi : ℕ → ℝ) (top : ℝ) (n : ℕ) : ℝ :=
  chi n - top * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)

theorem isLittleO_pow_mul_log (D : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h1 : (fun n : ℕ => Real.log ((n : ℝ) + 1)) =o[atTop] fun n : ℕ => (n : ℝ) + 1 :=
    Real.isLittleO_log_id_atTop.comp_tendsto ht
  have h2 : (fun n : ℕ => (n : ℝ) + 1) =O[atTop] fun n : ℕ => (n : ℝ) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  have h3 := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO (h1.trans_isBigO h2)
  exact h3.congr (fun n => rfl) (fun n => by ring)

theorem isEquivalent_add_pow (D j : ℕ) :
    (fun n : ℕ => ((n : ℝ) + j) ^ D) ~[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  have h1 : (fun _n : ℕ => (j : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) := by
    have : (fun _n : ℕ => (1 : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) := by
      rw [isLittleO_one_left_iff]
      simpa [Real.norm_eq_abs] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).congr' (Eventually.of_forall fun n => by simp)
    simpa using this.const_mul_left (j : ℝ)
  have h2 := (IsEquivalent.refl (u := fun n : ℕ => (n : ℝ)) (l := atTop)).add_isLittleO h1
  exact h2.pow D

theorem isLittleO_shift_pow_mul_log (D j : ℕ) :
    (fun n : ℕ => ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have h1 := (isLittleO_pow_mul_log D).comp_tendsto (tendsto_add_atTop_nat j)
  have h2 := (isEquivalent_add_pow (D + 1) j).isBigO
  have h3 := h1.trans_isBigO (h2.congr_left (fun n => by simp))
  exact h3

theorem isLittleO_succ_pow_sub (D : ℕ) :
    (fun n : ℕ => ((n : ℝ) + 1) ^ (D + 1) - (n : ℝ) ^ (D + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have h := (isEquivalent_add_pow (D + 1) 1).isLittleO
  exact h.congr (fun n => by simp) (fun n => rfl)

theorem powLog_mono (D : ℕ) {m n : ℕ} (h : m ≤ n) :
    (m : ℝ) ^ D * Real.log ((m : ℝ) + 1) ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hl0 : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hl : Real.log ((m : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  exact mul_le_mul (pow_le_pow_left₀ hm0 hmn D) hl hl0 (by positivity)

theorem powLog_nonneg (D n : ℕ) : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  have : (0 : ℝ) ≤ n := by positivity
  exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))

theorem chiP_add_sub_le (D : ℕ) (C : ℝ)
    (hC : ∀ n : ℕ, 1 ≤ n → chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1))
    (k n : ℕ) (hn : 1 ≤ n) :
    chiP D (n + k) - chiP D n ≤
      ∑ j ∈ Finset.range k, |C| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 := hC (n + k) (by omega)
    have h2 : C * (((n + k : ℕ) : ℝ) ^ D) * Real.log (((n + k : ℕ) : ℝ) + 1) ≤
        |C| * (((n + k : ℕ) : ℝ) ^ D * Real.log (((n + k : ℕ) : ℝ) + 1)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (powLog_nonneg D (n + k))
    have h3 : chiP D (n + (k + 1)) = chiP D (n + k + 1) := by rw [Nat.add_assoc]
    rw [h3]
    linarith

theorem hilbertSamuelDefect_projectiveSpace_abs_le (D : ℕ) (hh : ℝ) :
    ∃ C : ℝ, ∀ n : ℕ, |hsDefect D (chiP D) hh n| ≤ C * (n : ℝ) ^ (D + 1) := by
  obtain ⟨C, hC⟩ := exists_chiP_le D
  refine ⟨|C| + |hh|, fun n => ?_⟩
  have h0 := chiP_nonneg D n
  have h1 := hC n
  have hp : (0:ℝ) ≤ (n:ℝ) ^ (D + 1) := by positivity
  have hFpos : (0:ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have hf : (1:ℝ) ≤ ((D + 1).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hq : |hh * (n:ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)| ≤ |hh| * (n:ℝ) ^ (D + 1) := by
    rw [abs_div, abs_mul, abs_of_nonneg hp, abs_of_pos hFpos]
    exact div_le_self (by positivity) hf
  have hc : chiP D n ≤ |C| * (n:ℝ) ^ (D + 1) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
  have hq' := abs_le.mp hq
  unfold hsDefect
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg C, abs_nonneg hh]

theorem hilbertSamuelDefect_projectiveSpace_succ_sub_isLittleO (D : ℕ) (hh : ℝ) :
    (fun n => hsDefect D (chiP D) hh (n + 1) - hsDefect D (chiP D) hh n) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  obtain ⟨C, hC⟩ := exists_chiP_succ_sub_le D
  have hA : (fun n : ℕ => chiP D (n + 1) - chiP D n) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    refine IsBigO.trans_isLittleO ?_ (isLittleO_pow_mul_log D)
    refine IsBigO.of_bound |C| ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h0 := chiP_succ_sub_nonneg D n
    have h1 := hC n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, ← abs_mul]
    calc chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := h1
      _ = C * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by ring
      _ ≤ |C * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))| := le_abs_self _
  have hB := (isLittleO_succ_pow_sub D).const_mul_left (hh / ((D + 1).factorial : ℝ))
  refine (hA.sub hB).congr (fun n => ?_) (fun n => rfl)
  simp only [hsDefect]
  push_cast
  ring

theorem defect_of_sandwich (D k : ℕ) (δ hh C : ℝ) (hδ : 0 ≤ δ) (chi : ℕ → ℝ)
    (hlo : ∀ n : ℕ, k + 1 ≤ n → δ * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤ chi n)
    (hhi : ∀ n : ℕ, 1 ≤ n → chi n ≤ δ * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1)) :
    (fun n => hsDefect D chi (δ * hh) n - δ * hsDefect D (chiP D) hh n) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  obtain ⟨C', hC'⟩ := exists_chiP_succ_sub_le D
  set T : ℕ → ℝ := fun n =>
    ∑ j ∈ Finset.range k, |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1))
    with hT_def
  have hT : T =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    have := IsLittleO.fun_sum (s := Finset.range k)
      (A := fun j n => |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)))
      (fun j _ => (isLittleO_shift_pow_mul_log D j).const_mul_left |C'|)
    exact this
  have hW : (fun n : ℕ => δ * T n + |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) :=
    (hT.const_mul_left δ).add ((isLittleO_pow_mul_log D).const_mul_left |C|)
  refine IsBigO.trans_isLittleO ?_ hW
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have hX0 := powLog_nonneg D n
  have hCX : C * (n : ℝ) ^ D * Real.log (n + 1) ≤ |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hX0
  have hCX' : -(|C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := by
    rw [mul_assoc, neg_mul_eq_neg_mul]
    exact mul_le_mul_of_nonneg_right (neg_abs_le C) hX0
  have hT0 : 0 ≤ T n := Finset.sum_nonneg fun j _ =>
    mul_nonneg (abs_nonneg _) (powLog_nonneg D (n + j))

  have hup := hhi n (by omega)
  have hd1 := chiP_add_sub_le D C' hC' k n (by omega)
  have hd1' := mul_le_mul_of_nonneg_left hd1 hδ
  rw [mul_sub] at hd1'

  have hlow := hlo n hn
  have hm : n - k + k = n := by omega
  have hd2 := chiP_add_sub_le D C' hC' k (n - k) (by omega)
  rw [hm] at hd2
  have hTm : T (n - k) ≤ T n := by
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact powLog_mono D (by omega)
  have hd2' := mul_le_mul_of_nonneg_left (hd2.trans hTm) hδ
  rw [mul_sub] at hd2'
  have hTn : T n = ∑ j ∈ Finset.range k,
      |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)) := rfl
  rw [← hTn] at hd1'
  have hW0 : 0 ≤ δ * T n + |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) :=
    add_nonneg (mul_nonneg hδ hT0) (mul_nonneg (abs_nonneg _) hX0)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hW0, one_mul, abs_le]
  have he : hsDefect D chi (δ * hh) n - δ * hsDefect D (chiP D) hh n = chi n - δ * chiP D n := by
    simp only [hsDefect]; ring
  rw [he]
  constructor <;> linarith

theorem le_of_frequently_le (D : ℕ) (chi₁ chi₂ e : ℕ → ℝ) (t₁ t₂ s : ℝ)
    (h₁ : hsDefect D chi₁ t₁ =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (h₂ : hsDefect D chi₂ t₂ =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (he : e =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (hle : ∃ᶠ n : ℕ in atTop,
      chi₁ n ≤ chi₂ n + s * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) + e n) :
    t₁ ≤ t₂ + s := by
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have hF : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  set ε : ℝ := (t₁ - t₂ - s) / ((D + 1).factorial : ℝ) with hε_def
  have hε : 0 < ε := div_pos (by linarith) hF
  have hb := ((h₁.sub h₂).sub he).def (half_pos hε)
  obtain ⟨n, hn, hb', h1⟩ := (hle.and_eventually (hb.and (eventually_ge_atTop 1))).exists
  have hP : (0 : ℝ) < (n : ℝ) ^ (D + 1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast h1
    positivity
  simp only [Real.norm_eq_abs, abs_of_pos hP] at hb'
  have hb2 := (abs_le.mp hb').1
  unfold hsDefect at hb2
  have key : ε * (n : ℝ) ^ (D + 1) = t₁ * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)
      - t₂ * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)
      - s * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by
    rw [hε_def]; field_simp
  have : 0 < ε / 2 * (n : ℝ) ^ (D + 1) := by positivity
  linarith

theorem rank_mul_isLittleO (D : ℕ) (r : ℕ → ℝ) (δ t : ℝ)
    (hr : (fun n : ℕ => r n - δ * (n : ℝ) ^ D / (D.factorial : ℝ)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ D) :
    (fun n : ℕ => (n : ℝ) * r n * t -
        ((D + 1 : ℝ) * δ * t) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have h := ((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left t).mul_isLittleO hr
  refine h.congr (fun n => ?_) (fun n => by ring)
  have hD : (0 : ℝ) < (D.factorial : ℝ) := by positivity
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

end ReciprocityTheory.GeometryOfNumbersTheory
