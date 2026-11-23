import Mathlib
import Formalism.IncomingBounds.LevelTail

noncomputable section
open scoped BigOperators
open Finset fwdDiff

namespace Formalism.IncomingBounds

theorem altChoose_sum_eq_zero (D s y : ℕ) (hs : s ≤ D) :
    ∑ k ∈ range (D + 1 + 1), ((-1 : ℤ) ^ (D + 1 - k) * ((D + 1).choose k : ℤ)) *
      (((y + k).choose s : ℕ) : ℤ) = 0 := by
  have h := fwdDiff_iter_eq_sum_shift (1 : ℕ) (fun x ↦ (x.choose s : ℤ)) (D + 1) y
  have hz : (fwdDiff (1 : ℕ))^[D + 1] (fun x ↦ (x.choose s : ℤ) : ℕ → ℤ) y = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, D + 1 = (k + 1) + s := ⟨D - s, by omega⟩
    rw [hk, Function.iterate_add_apply]
    have h0 := fwdDiff_iter_choose 0 s
    simp only [add_zero] at h0
    rw [h0]
    simp only [Nat.choose_zero_right, Nat.cast_one, Function.iterate_succ_apply, fwdDiff_const]
    rw [fwdDiff_iter_eq_sum_shift]
    simp
  rw [hz] at h
  simpa [smul_eq_mul] using h.symm

theorem top_radius_holds : TopRadius := by
  intro l hl A cap J hA hcap hJ
  set T := (Finset.range J).filter Odd with hT
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hlpos : (0 : ℝ) < l := by linarith
  have hpow : ∀ n : ℕ, (0 : ℝ) < (l : ℝ) ^ n := fun n => pow_pos hlpos n
  have hle1 : ∀ j k : ℕ, max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 ≤ 1 := by
    intro j k
    apply max_le _ zero_le_one
    have : 0 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹ := by positivity
    linarith
  let S := T.filter (fun j => A / (l : ℝ) ^ j ≤ cap j)
  by_cases hS : S.Nonempty
  · obtain ⟨k, hkS, hkmin⟩ : ∃ k ∈ S, ∀ j ∈ S, k ≤ j :=
      ⟨S.min' hS, S.min'_mem hS, fun j hj => S.min'_le j hj⟩
    have hkT : k ∈ T := (Finset.mem_filter.mp hkS).1
    have hkJ : k < J := Finset.mem_range.mp (Finset.mem_filter.mp hkT).1
    have hkcap : A / (l : ℝ) ^ k ≤ cap k := (Finset.mem_filter.mp hkS).2
    refine ⟨((l : ℝ) ^ k)⁻¹, ?_, ?_⟩
    · exact inv_anti₀ (hpow k) (pow_le_pow_right₀ hl1 hkJ.le)
    · have hterm : ∀ j ∈ T, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 +
          (if j = k then A * ((l : ℝ) ^ k)⁻¹ else 0) ≤ min (cap j) (A / (l : ℝ) ^ j) := by
        intro j hj
        rcases lt_trichotomy j k with hjk | hjk | hjk
        · have hjS : j ∉ S := fun h => absurd (hkmin j h) (by omega)
          have hlt : cap j < A / (l : ℝ) ^ j := by
            by_contra hc
            push Not at hc
            exact hjS (Finset.mem_filter.mpr ⟨hj, hc⟩)
          rw [if_neg (by omega), add_zero, min_eq_left hlt.le]
          calc cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 ≤ cap j * 1 :=
                mul_le_mul_of_nonneg_left (hle1 j k) (hcap j)
            _ = cap j := mul_one _
        · subst hjk
          rw [if_pos rfl, mul_inv_cancel₀ (hpow j).ne', sub_self, max_self, mul_zero, zero_add,
            min_eq_right hkcap, div_eq_mul_inv]
        · have h1 : 1 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ (hpow k), one_mul]
            exact pow_le_pow_right₀ hl1 hjk.le
          rw [if_neg (by omega), add_zero, max_eq_right (by linarith), mul_zero]
          exact le_min (hcap j) (div_nonneg hA (hpow j).le)
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hkT] at hsum
      have : 0 ≤ A / (l : ℝ) ^ J := div_nonneg hA (hpow J).le
      linarith
  · have hS' : ∀ j ∈ T, cap j < A / (l : ℝ) ^ j := by
      intro j hj
      by_contra hc
      push Not at hc
      exact hS ⟨j, Finset.mem_filter.mpr ⟨hj, hc⟩⟩
    refine ⟨((l : ℝ) ^ J)⁻¹, le_rfl, ?_⟩
    have hterm : ∀ j ∈ T, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ J)⁻¹) 0 ≤
        min (cap j) (A / (l : ℝ) ^ j) := by
      intro j hj
      rw [min_eq_left (hS' j hj).le]
      calc cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ J)⁻¹) 0 ≤ cap j * 1 :=
            mul_le_mul_of_nonneg_left (hle1 j J) (hcap j)
        _ = cap j := mul_one _
    have hsum := Finset.sum_le_sum hterm
    rw [div_eq_mul_inv A]
    linarith

theorem newton_window_holds : NewtonWindow := by
  intro R _ I D a y0 hwin
  let f : ℕ → R := fun y => ∑ s ∈ range (D + 1), a s * ((Nat.choose y s : ℕ) : R)
  let c : ℕ → ℤ := fun k => (-1 : ℤ) ^ (D + 1 - k) * (((D + 1).choose k : ℕ) : ℤ)
  have hsm : ∀ (z : ℤ) (x : R), x ∈ I → (z : R) * x ∈ I := by
    intro z x hx
    rw [← zsmul_eq_mul]
    exact I.zsmul_mem hx z
  have hZ : ∀ y s, s ≤ D →
      ∑ k ∈ range (D + 1 + 1), (c k : R) * (((y + k).choose s : ℕ) : R) = 0 := by
    intro y s hs
    have := congrArg (Int.cast : ℤ → R) (altChoose_sum_eq_zero D s y hs)
    push_cast at this
    simpa [c] using this
  have hE : ∀ y, ∑ k ∈ range (D + 1 + 1), (c k : R) * f (y + k) = 0 := by
    intro y
    have hk : ∀ k, (c k : R) * f (y + k) =
        ∑ s ∈ range (D + 1), a s * ((c k : R) * (((y + k).choose s : ℕ) : R)) := by
      intro k
      simp only [f, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    simp_rw [hk]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro s hs
    rw [← Finset.mul_sum, hZ y s (by simp at hs; omega), mul_zero]
  have hup : ∀ t, f (y0 + t) ∈ I := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      by_cases ht : t ≤ D
      · exact hwin t ht
      · obtain ⟨u, rfl⟩ : ∃ u, t = u + (D + 1) := ⟨t - (D + 1), by omega⟩
        have h := hE (y0 + u)
        rw [Finset.sum_range_succ] at h
        have hc : (c (D + 1) : R) = 1 := by simp [c]
        rw [hc, one_mul] at h
        have hmem : ∑ k ∈ range (D + 1), (c k : R) * f (y0 + u + k) ∈ I := by
          apply AddSubgroup.sum_mem
          intro k hk
          apply hsm
          have := ih (u + k) (by simp at hk; omega)
          rwa [← add_assoc] at this
        have : f (y0 + (u + (D + 1))) = -(∑ k ∈ range (D + 1), (c k : R) * f (y0 + u + k)) := by
          rw [← add_assoc]
          linear_combination h
        rw [this]
        exact I.neg_mem hmem
  have hc0i : c 0 * c 0 = 1 := by
    simp only [c, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, ← mul_pow]
    simp
  have hc0 : (c 0 : R) * (c 0 : R) = 1 := by
    rw [← Int.cast_mul, hc0i, Int.cast_one]
  have hdown : ∀ m y, y0 ≤ y + m → f y ∈ I := by
    intro m
    induction m with
    | zero =>
      intro y hy
      obtain ⟨t, rfl⟩ : ∃ t, y = y0 + t := ⟨y - y0, by omega⟩
      exact hup t
    | succ m ih =>
      intro y hy
      have h := hE y
      rw [Finset.sum_range_succ'] at h
      simp only [add_zero] at h
      have hmem : ∑ k ∈ range (D + 1), (c (k + 1) : R) * f (y + (k + 1)) ∈ I := by
        apply AddSubgroup.sum_mem
        intro k _
        apply hsm
        apply ih
        omega
      have : f y = (c 0 : R) * (-(∑ k ∈ range (D + 1), (c (k + 1) : R) * f (y + (k + 1)))) := by
        linear_combination (c 0 : R) * h - (f y) * hc0
      rw [this]
      exact hsm _ _ (I.neg_mem hmem)
  intro y
  exact hdown y0 y (by omega)

end Formalism.IncomingBounds
