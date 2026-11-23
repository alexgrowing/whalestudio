import Mathlib
import Formalism.PieriBlockIdeals.Statement

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

lemma sums_harmonic_real (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ≤ 1 + Real.log n := by
  have h1 := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at h1
  push_cast at h1
  simpa [one_div] using h1

lemma leastCongruentPos_mem_le (l D : ℕ) (hD : 1 ≤ D) :
    1 ≤ d0 l (D : ℤ) ∧ (l : ℤ) ∣ (D : ℤ) - (d0 l (D : ℤ) : ℤ) ∧ d0 l (D : ℤ) ≤ D := by
  have hmem : D ∈ {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ (D : ℤ) - (d : ℤ)} := ⟨hD, by simp⟩
  have hs := Nat.sInf_mem (⟨D, hmem⟩ : ({d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ (D : ℤ) - (d : ℤ)}).Nonempty)
  unfold d0
  exact ⟨hs.1, hs.2, Nat.sInf_le hmem⟩

lemma sums_le_of_gate (l D : ℕ) (hD : 1 ≤ D) (hg : ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)) :
    (l : ℤ) ≤ (D : ℤ) - (d0 l (D : ℤ) : ℤ) := by
  obtain ⟨_, hdvd, _⟩ := leastCongruentPos_mem_le l D hD
  exact Int.le_of_dvd (by omega) hdvd

lemma sums_inj (D h : ℕ) (L : ℝ) (hD : 1 ≤ D) (hDh : D ≤ h) (hh : (h : ℝ) < L ^ 2)
    (hL : 1 ≤ L) (l l' : ℕ) (hl : l.Prime) (hl' : l'.Prime) (hLl : L < (l : ℝ))
    (hLl' : L < (l' : ℝ)) (hg : ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))
    (heq : d0 l (D : ℤ) = d0 l' (D : ℤ)) : l = l' := by
  by_contra hne
  obtain ⟨_, hdvd, _⟩ := leastCongruentPos_mem_le l D hD
  obtain ⟨_, hdvd', _⟩ := leastCongruentPos_mem_le l' D hD
  rw [← heq] at hdvd'
  have hcop : IsCoprime (l : ℤ) (l' : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes hl hl').2 hne
  have hprod := hcop.mul_dvd hdvd hdvd'
  have hpos : (0 : ℤ) < (D : ℤ) - (d0 l (D : ℤ) : ℤ) := by omega
  have hle2 := Int.le_of_dvd hpos hprod
  have hZ : (l : ℤ) * (l' : ℤ) ≤ (h : ℤ) := by
    have : (D : ℤ) ≤ h := by exact_mod_cast hDh
    have : (0 : ℤ) ≤ (d0 l (D : ℤ) : ℤ) := by positivity
    linarith
  have hR : (l : ℝ) * (l' : ℝ) ≤ (h : ℝ) := by exact_mod_cast hZ
  have hL0 : 0 ≤ L := by linarith
  have : L ^ 2 < (l : ℝ) * (l' : ℝ) := by
    rw [sq]; exact mul_lt_mul'' hLl hLl' hL0 hL0
  linarith

theorem gatedPrimeSum_holds : GatedSum := by
  intro D h L A k P hD hDh hA hk hh hL hP
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast le_trans hD hDh
  have hlogh : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg hh1
  have step1 : ∑ l ∈ P, (if ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ) then
        min k (A / (d0 l (D : ℤ) : ℝ)) else 0) * Real.log (l : ℝ) ≤
      ∑ l ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
        (A / (d0 l (D : ℤ) : ℝ)) * Real.log (h : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro l hl
    obtain ⟨hlp, _⟩ := hP l hl
    split_ifs with hgl
    · have hsub := sums_le_of_gate l D hD hgl
      have hlh : (l : ℝ) ≤ (h : ℝ) := by
        have h1 : (l : ℤ) ≤ (h : ℤ) := by
          have : (D : ℤ) ≤ (h : ℤ) := by exact_mod_cast hDh
          have : (0 : ℤ) ≤ ((d0 l (D : ℤ) : ℕ) : ℤ) := by positivity
          linarith
        exact_mod_cast h1
      have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hlp.one_lt.le
      exact mul_le_mul (min_le_right _ _) (Real.log_le_log (by linarith) hlh)
        (Real.log_nonneg hl1) (div_nonneg hA (Nat.cast_nonneg _))
    · simp
  have hinj : ∀ x ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
      ∀ y ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
      d0 x (D : ℤ) = d0 y (D : ℤ) → x = y := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.1 hx
    have hy' := Finset.mem_filter.1 hy
    obtain ⟨hxp, hLx⟩ := hP x hx'.1
    obtain ⟨hyp, hLy⟩ := hP y hy'.1
    exact sums_inj D h L hD hDh hh hL x y hxp hyp hLx hLy hx'.2 hxy
  have step2 : ∑ l ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
        (A / (d0 l (D : ℤ) : ℝ)) * Real.log (h : ℝ) =
      ∑ x ∈ (P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))).image
        (fun l => d0 l (D : ℤ)), (A / (x : ℝ)) * Real.log (h : ℝ) := by
    rw [Finset.sum_image hinj]
  have hsub : (P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))).image
      (fun l => d0 l (D : ℤ)) ⊆ Finset.Icc 1 h := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, _, h2⟩ := leastCongruentPos_mem_le l D hD
    exact Finset.mem_Icc.2 ⟨h1, le_trans h2 hDh⟩
  have step3 : ∑ x ∈ (P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))).image
        (fun l => d0 l (D : ℤ)), (A / (x : ℝ)) * Real.log (h : ℝ) ≤
      ∑ x ∈ Finset.Icc 1 h, (A / (x : ℝ)) * Real.log (h : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => mul_nonneg (div_nonneg hA (Nat.cast_nonneg _)) hlogh)
  have step4 : ∑ x ∈ Finset.Icc 1 h, (A / (x : ℝ)) * Real.log (h : ℝ) =
      A * Real.log (h : ℝ) * ∑ x ∈ Finset.Icc 1 h, (1 : ℝ) / (x : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hH := sums_harmonic_real h
  have hAl : 0 ≤ A * Real.log (h : ℝ) := mul_nonneg hA hlogh
  refine le_trans step1 ?_
  rw [step2]
  refine le_trans step3 ?_
  rw [step4]
  calc A * Real.log (h : ℝ) * ∑ x ∈ Finset.Icc 1 h, (1 : ℝ) / (x : ℝ)
      ≤ A * Real.log (h : ℝ) * (1 + Real.log h) := mul_le_mul_of_nonneg_left hH hAl
    _ = A * (1 + Real.log (h : ℝ)) * Real.log (h : ℝ) := by ring

def sums_G (c x0 x : ℝ) : ℝ := if x ≤ x0 then c / x0 * x else c + c * Real.log (x / x0)

lemma sums_step (c x0 : ℝ) (hc : 0 < c) (hx0 : 0 < x0) (d : ℕ) (hd : 1 ≤ d) :
    min (c / x0) (c / (d : ℝ)) ≤ sums_G c x0 d - sums_G c x0 ((d : ℝ) - 1) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hd' : (d : ℝ) ≠ 0 := hdpos.ne'
  have hx0' : x0 ≠ 0 := hx0.ne'
  unfold sums_G
  by_cases h1 : (d : ℝ) ≤ x0
  · have h2 : (d : ℝ) - 1 ≤ x0 := by linarith
    rw [if_pos h1, if_pos h2]
    have e : c / x0 * d - c / x0 * (d - 1) = c / x0 := by ring
    rw [e]
    exact min_le_left _ _
  · rw [not_le] at h1
    by_cases h2 : (d : ℝ) - 1 ≤ x0
    · rw [if_neg (not_le.2 h1), if_pos h2]
      refine le_trans (min_le_right _ _) ?_
      have hlog : 1 - x0 / d ≤ Real.log (d / x0) := by
        have := Real.one_sub_inv_le_log_of_pos (div_pos hdpos hx0)
        rwa [inv_div] at this
      have hq : 0 ≤ (d - x0) * (x0 - (d - 1)) := mul_nonneg (by linarith) (by linarith)
      have e : c + c * (1 - x0 / d) - c / x0 * (d - 1) - c / d =
          c * ((d - x0) * (x0 - (d - 1))) / (x0 * d) := by
        field_simp
        ring
      have hnn : 0 ≤ c * ((d - x0) * (x0 - (d - 1))) / (x0 * d) :=
        div_nonneg (mul_nonneg hc.le hq) (mul_pos hx0 hdpos).le
      have hcl := mul_le_mul_of_nonneg_left hlog hc.le
      linarith
    · rw [not_le] at h2
      rw [if_neg (not_le.2 h1), if_neg (not_le.2 h2)]
      refine le_trans (min_le_right _ _) ?_
      have hdm : 0 < (d : ℝ) - 1 := by linarith
      have hdm' : (d : ℝ) - 1 ≠ 0 := hdm.ne'
      have hlog : Real.log (d / x0) - Real.log ((d - 1) / x0) = Real.log (d / (d - 1)) := by
        rw [Real.log_div hd' hx0', Real.log_div hdm' hx0', Real.log_div hd' hdm']
        ring
      have hlog' : c * Real.log (d / x0) - c * Real.log ((d - 1) / x0) = c * Real.log (d / (d - 1)) := by
        rw [← mul_sub, hlog]
      have hlb : 1 - (d - 1) / d ≤ Real.log (d / (d - 1)) := by
        have := Real.one_sub_inv_le_log_of_pos (div_pos hdpos hdm)
        rwa [inv_div] at this
      have e : c / d = c * (1 - (d - 1) / d) := by
        rw [one_sub_div hd']
        ring
      have hcl := mul_le_mul_of_nonneg_left hlb hc.le
      rw [e]
      linarith

lemma sums_tele (F : ℝ → ℝ) (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, (F (d : ℝ) - F ((d : ℝ) - 1)) = F n - F 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    rw [add_sub_cancel_right]
    ring

theorem harmonicMinSum_holds : SharperSize := by
  intro k m h hm hmk hh
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le hm hmk)
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hmk' : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hk' : (k : ℝ) ≠ 0 := hk0.ne'
  have hc : 0 < (m : ℝ) * h := mul_pos hm0 hh0
  have hx0 : 0 < (m : ℝ) * h / k := div_pos hc hk0
  have hck : (m : ℝ) * h / ((m : ℝ) * h / k) = k := by
    rw [div_div_eq_mul_div, div_eq_iff hc.ne']
    ring
  have hterm : ∀ d ∈ Finset.Icc 1 h, min (k : ℝ) (((m : ℝ) * h) / d) ≤
      sums_G ((m : ℝ) * h) ((m : ℝ) * h / k) d -
        sums_G ((m : ℝ) * h) ((m : ℝ) * h / k) ((d : ℝ) - 1) := by
    intro d hd
    have := sums_step ((m : ℝ) * h) ((m : ℝ) * h / k) hc hx0 d
      (Finset.mem_Icc.1 hd).1
    rwa [hck] at this
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [sums_tele]
  have h0 : sums_G ((m : ℝ) * h) ((m : ℝ) * h / k) 0 = 0 := by
    unfold sums_G
    rw [if_pos hx0.le]
    ring
  rw [h0, sub_zero]
  unfold sums_G
  split_ifs with hle
  · rw [hck]
    have hkm : (k : ℝ) * h ≤ (m : ℝ) * h := by
      have h1 := mul_le_mul_of_nonneg_left hle hk0.le
      have e : (k : ℝ) * ((m : ℝ) * h / k) = (m : ℝ) * h := by
        field_simp
      linarith
    have hlog : 0 ≤ Real.log ((k : ℝ) / m) := Real.log_nonneg ((one_le_div hm0).2 hmk')
    nlinarith [mul_nonneg hc.le hlog]
  · have e : (h : ℝ) / ((m : ℝ) * h / k) = k / m := by
      rw [div_div_eq_mul_div, div_eq_div_iff hc.ne' hm0.ne']
      ring
    rw [e]
    exact le_of_eq (by ring)

theorem SharperSizeNeedsMleK_false : ¬ SharperSizeNeedsMleK := by
  intro H
  have key := H 1 2 1 (by norm_num) (by norm_num) (by norm_num)
  have h1 : ∑ d ∈ Finset.Icc (1 : ℕ) 1, min ((1 : ℕ) : ℝ) ((((2 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) / (d : ℝ)) = 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton]
    norm_num
  have h2 : Real.log (((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = - Real.log 2 := by
    push_cast
    rw [one_div, Real.log_inv]
  rw [h1, h2] at key
  have hl := Real.log_two_gt_d9
  push_cast at key
  linarith

end Formalism.CohomologicalDescent
