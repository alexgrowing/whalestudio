import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset MeasureTheory

theorem weight_shift_product : OppositeSignRhoDifferenceEqCard := by
  intro N sg rhoN a b hab hs
  have h1 : (univ.filter (fun c => a < c ∧ sg c ≠ sg a)).card =
      (univ.filter (fun e => a < e ∧ e < b ∧ sg e ≠ sg a)).card +
        (univ.filter (fun c => b < c ∧ sg c ≠ sg b)).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨h, h'⟩
        rcases lt_trichotomy c b with hc | hc | hc
        · exact Or.inl ⟨h, hc, h'⟩
        · exact absurd (hc ▸ hs.symm) h'
        · exact Or.inr ⟨hc, hs ▸ h'⟩
      · rintro (⟨h, _, h'⟩ | ⟨h, h'⟩)
        · exact ⟨h, h'⟩
        · exact ⟨hab.trans h, hs ▸ h'⟩
    · rw [disjoint_left]
      intro c hc hc'
      simp only [mem_filter, mem_univ, true_and] at hc hc'
      exact absurd hc.2.1 (not_lt.mpr hc'.1.le)
  have h2 : (univ.filter (fun c => c < b ∧ sg c ≠ sg b)).card =
      (univ.filter (fun e => a < e ∧ e < b ∧ sg e ≠ sg a)).card +
        (univ.filter (fun c => c < a ∧ sg c ≠ sg a)).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨h, h'⟩
        rcases lt_trichotomy c a with hc | hc | hc
        · exact Or.inr ⟨hc, hs ▸ h'⟩
        · exact absurd (hc ▸ hs) h'
        · exact Or.inl ⟨hc, h, hs ▸ h'⟩
      · rintro (⟨_, h, h'⟩ | ⟨h, h'⟩)
        · exact ⟨h, hs ▸ h'⟩
        · exact ⟨h.trans hab, hs ▸ h'⟩
    · rw [disjoint_left]
      intro c hc hc'
      simp only [mem_filter, mem_univ, true_and] at hc hc'
      exact absurd hc.1 (not_lt.mpr hc'.1.le)
  simp only [rhoN]
  rw [h1, h2]
  push_cast
  ring

private lemma exp_quadratic_lower_bound {y ε : ℝ} (hε1 : ε ≤ 1) (hy : |y| ≤ ε) :
    1 + y + y ^ 2 / 2 * (1 - 4 * ε / 9) ≤ Real.exp y := by
  have hy1 : |y| ≤ 1 := hy.trans hε1
  have hb := Real.exp_bound hy1 (n := 3) (by norm_num)
  have hsum : ∑ m ∈ range 3, y ^ m / (m.factorial : ℝ) = 1 + y + y ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  have hc : |y| ^ 3 * (((3 : ℕ).succ : ℝ) / (((3 : ℕ).factorial : ℝ) * (3 : ℕ))) = |y| ^ 3 * (2 / 9) := by
    norm_num [Nat.factorial]
  rw [hc] at hb
  have h3 : |y| ^ 3 ≤ y ^ 2 * ε := by
    have : |y| ^ 3 = y ^ 2 * |y| := by rw [← sq_abs y]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hy (sq_nonneg y)
  have := (abs_le.mp hb).1
  nlinarith

theorem cumulant_expansion : CumulantLowerBound := by
  intro ι _ P y ε hP hP1 hmean hε0 hε1 hy
  set V : ℝ := ∑ j, P j * y j ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun j _ => mul_nonneg (hP j) (sq_nonneg _)
  have hVε : V ≤ ε ^ 2 := by
    calc V ≤ ∑ j, P j * ε ^ 2 := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hP j)
          exact sq_le_sq' (by linarith [(abs_le.mp (hy j)).1]) (abs_le.mp (hy j)).2
      _ = ε ^ 2 := by rw [← Finset.sum_mul, hP1, one_mul]
  set z : ℝ := V / 2 * (1 - 4 * ε / 9) with hz
  have hS : 1 + z ≤ ∑ j, P j * Real.exp (y j) := by
    calc 1 + z = ∑ j, P j * (1 + y j + y j ^ 2 / 2 * (1 - 4 * ε / 9)) := by
          have : ∀ j, P j * (1 + y j + y j ^ 2 / 2 * (1 - 4 * ε / 9)) =
              P j + P j * y j + (P j * y j ^ 2) * ((1 - 4 * ε / 9) / 2) := fun j => by ring
          simp only [this]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hP1, hmean, ← hV, hz]
          ring
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (exp_quadratic_lower_bound hε1 (hy j)) (hP j)
  have hc0 : 0 ≤ 1 - 4 * ε / 9 := by linarith
  have hz0 : 0 ≤ z := mul_nonneg (by linarith) hc0
  have h1z : 0 < 1 + z := by linarith
  have hlog : Real.log (1 + z) ≤ Real.log (∑ j, P j * Real.exp (y j)) := Real.log_le_log h1z hS
  have hinv := Real.one_sub_inv_le_log_of_pos h1z
  have hzz : z * (1 - z) ≤ 1 - (1 + z)⁻¹ := by
    have : 1 - (1 + z)⁻¹ = z / (1 + z) := by field_simp; ring
    rw [this, le_div_iff₀ h1z]
    nlinarith [mul_nonneg hz0 (mul_nonneg hz0 hz0)]
  have hzV : z ≤ ε / 2 := by
    have h1 : z ≤ V / 2 := by
      rw [hz]; nlinarith
    have h2 : ε ^ 2 ≤ ε := by nlinarith
    linarith
  have hfin : V / 2 * (1 - ε) ≤ z * (1 - z) := by
    have h1 : z * (1 - ε / 2) ≤ z * (1 - z) := mul_le_mul_of_nonneg_left (by linarith) hz0
    have h2 : V / 2 * (1 - ε) ≤ z * (1 - ε / 2) := by
      rw [hz, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      nlinarith [mul_nonneg hε0 hε0]
    linarith
  linarith

private lemma matrix_rank_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℂ (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank ℂ ((LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :
          Submodule ℂ (Fin n → ℂ))) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

theorem rank_formula : RankLeTwiceMin := by
  intro N sg X hX
  classical
  set Dp : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun a => if sg a = true then 1 else 0) with hDp
  set Dm : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun a => if sg a = false then 1 else 0) with hDm
  have hrp : Dp.rank = (univ.filter (fun a => sg a = true)).card := by
    rw [hDp, Matrix.rank_diagonal, Fintype.card_subtype]
    congr 1
    ext a
    simp
  have hrm : Dm.rank = (univ.filter (fun a => sg a = false)).card := by
    rw [hDm, Matrix.rank_diagonal, Fintype.card_subtype]
    congr 1
    ext a
    simp
  have hdec : X = Dp * X * Dm + Dm * X * Dp := by
    ext a b
    rw [Matrix.add_apply, hDp, hDm, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.diagonal_mul]
    by_cases hs : sg a = sg b
    · rw [hX a b hs]; simp
    · cases ha : sg a <;> cases hb : sg b <;> simp_all
  have h1 : (Dp * X * Dm).rank ≤ min Dp.rank Dm.rank := by
    refine le_min ?_ (Matrix.rank_mul_le_right _ _)
    rw [Matrix.mul_assoc]
    exact Matrix.rank_mul_le_left _ _
  have h2 : (Dm * X * Dp).rank ≤ min Dp.rank Dm.rank := by
    refine le_min (Matrix.rank_mul_le_right _ _) ?_
    rw [Matrix.mul_assoc]
    exact Matrix.rank_mul_le_left _ _
  calc X.rank = (Dp * X * Dm + Dm * X * Dp).rank := by rw [← hdec]
    _ ≤ (Dp * X * Dm).rank + (Dm * X * Dp).rank := matrix_rank_add_le _ _
    _ ≤ _ := by rw [hrp, hrm] at h1 h2; omega

private lemma sum_ico_telescoping_plus_one (L : ℕ → ℝ) (b a : ℕ) (h : b ≤ a) :
    ∑ i ∈ Ico b a, (L i - L (i + 1) + 1) = L b - L a + ((a : ℝ) - b) := by
  induction a, h using Nat.le_induction with
  | base => simp
  | succ a h ih =>
    rw [Finset.sum_Ico_succ_top h, ih]
    push_cast
    ring

theorem weighted_sum_eq_quadratic_form : WeightedSumEqQuadraticForm := by
  intro N lam sg X hX P V
  have hent : ∀ (i : ℕ) (a b : Fin N), ((1 - P i) * X * P i) a b =
      if i ≤ a.val ∧ b.val < i then X a b else 0 := by
    intro i a b
    have h1 : (1 - P i) = Matrix.diagonal (fun a : Fin N => if a.val < i then (0 : ℂ) else 1) := by
      ext c d
      by_cases hcd : c = d
      · subst hcd
        by_cases hc : c.val < i <;> simp [P, hc]
      · simp [P, hcd]
    rw [h1]
    simp only [P]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases ha : a.val < i <;> by_cases hb : b.val < i <;> simp [ha, hb, not_le.mpr, not_lt.mp]
  have hV : ∀ i, V i = ∑ a, ∑ b, if i ≤ a.val ∧ b.val < i then ‖X a b‖ ^ 2 else 0 := by
    intro i
    simp only [V]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hent]
    split_ifs <;> simp
  set L : ℕ → ℝ := fun n => if h : n < N then lam ⟨n, h⟩ else 0 with hL
  have hLv : ∀ a : Fin N, L a.val = lam a := fun a => by simp [hL]
  have hterm : ∀ i : Fin N,
      (if h : i.val + 1 < N then (lam i - lam ⟨i.val + 1, h⟩ + 1) * V (i.val + 1) else 0) =
      ∑ a : Fin N, ∑ b : Fin N, (if i.val ∈ Ico b.val a.val then (L i.val - L (i.val + 1) + 1) else 0)
        * ‖X a b‖ ^ 2 := by
    intro i
    split_ifs with h
    · rw [hV, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have e1 : L (i.val + 1) = lam ⟨i.val + 1, h⟩ := by simp [hL, h]
      rw [hLv, e1]
      by_cases hc : i.val + 1 ≤ a.val ∧ b.val < i.val + 1
      · have : i.val ∈ Ico b.val a.val := by rw [mem_Ico]; omega
        rw [if_pos hc, if_pos this]
      · have : i.val ∉ Ico b.val a.val := by rw [mem_Ico]; omega
        rw [if_neg hc, if_neg this]; ring
    · symm
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      have : i.val ∉ Ico b.val a.val := by
        rw [mem_Ico]; have := a.isLt; omega
      rw [if_neg this, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ i : Fin N, (if i.val ∈ Ico b.val a.val then (L i.val - L (i.val + 1) + 1) else 0) =
      ∑ i ∈ Ico b.val a.val, (L i - L (i + 1) + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i ∈ Ico b.val a.val then (L i - L (i + 1) + 1) else 0) N,
      ← Finset.sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    have := a.isLt
    omega
  rw [hsum]
  by_cases hba : b < a
  · rw [sum_ico_telescoping_plus_one L _ _ (Fin.le_def.mp hba.le), hLv, hLv]
    by_cases hs : sg a = sg b
    · rw [hX a b hs]; simp [hs]
    · rw [if_pos ⟨hba, hs⟩]
  · have : Ico b.val a.val = ∅ := Finset.Ico_eq_empty (fun h => hba (Fin.lt_def.mpr h))
    rw [this, if_neg (fun h => hba h.1)]
    simp

end Formalism.HermitianLattices.GenusMassVolumes
