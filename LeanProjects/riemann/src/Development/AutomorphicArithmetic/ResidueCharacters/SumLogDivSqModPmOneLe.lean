import Mathlib

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces.Sums

open Real Finset

lemma filter_sub_Icc (T : Finset ℕ) (Y : ℝ) :
    T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y) ⊆ Finset.Icc 1 ⌊Y⌋₊ := by
  intro l hl
  simp only [Finset.mem_filter] at hl
  rw [Finset.mem_Icc]
  exact ⟨hl.2.1, Nat.le_floor hl.2.2⟩

theorem sum_log_le (T : Finset ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l ≤ Y * Real.log Y := by
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have h1 : ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l ≤
      (T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card • Real.log Y := by
    apply Finset.sum_le_card_nsmul
    intro l hl
    simp only [Finset.mem_filter] at hl
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl.2.1
    exact Real.log_le_log (by linarith) hl.2.2
  have h2 : ((T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card : ℝ) ≤ Y := by
    have := Finset.card_le_card (filter_sub_Icc T Y)
    rw [Nat.card_Icc] at this
    have h3 : ((T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by
      exact_mod_cast (by omega : (T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y)).card ≤ ⌊Y⌋₊)
    exact h3.trans (Nat.floor_le (by linarith))
  rw [nsmul_eq_mul] at h1
  nlinarith

theorem sum_log_div_le (T : Finset ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / l ≤ (1 + Real.log Y) ^ 2 := by
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  calc ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / l
      ≤ ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log Y * ((l : ℝ))⁻¹ := by
        apply Finset.sum_le_sum
        intro l hl
        simp only [Finset.mem_filter] at hl
        have : (1 : ℝ) ≤ l := by exact_mod_cast hl.2.1
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Real.log_le_log (by linarith) hl.2.2) (by positivity)
    _ ≤ ∑ l ∈ Finset.Icc 1 ⌊Y⌋₊, Real.log Y * ((l : ℝ))⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (filter_sub_Icc T Y)
        intro l _ _
        positivity
    _ = Real.log Y * (harmonic ⌊Y⌋₊ : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        push_cast
        rfl
    _ ≤ Real.log Y * (1 + Real.log ⌊Y⌋₊) := by
        exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) hlogY
    _ ≤ Real.log Y * (1 + Real.log Y) := by
        have hf : (1 : ℝ) ≤ ⌊Y⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hY)
        have : Real.log ⌊Y⌋₊ ≤ Real.log Y := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
        nlinarith
    _ ≤ (1 + Real.log Y) ^ 2 := by nlinarith

theorem sum_log_div_pred_le (T : Finset ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / ((l : ℝ) - 1) ≤ 2 * (1 + Real.log Y) ^ 2 := by
  calc ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / ((l : ℝ) - 1)
      ≤ ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l : ℝ) ≤ Y), 2 * (Real.log l / l) := by
        apply Finset.sum_le_sum
        intro l hl
        simp only [Finset.mem_filter] at hl
        have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.2.1
        have hlog : 0 ≤ Real.log l := Real.log_nonneg (by linarith)
        rw [div_le_iff₀ (by linarith)]
        rw [show 2 * (Real.log l / l) * ((l : ℝ) - 1) = Real.log l * (2 * ((l : ℝ) - 1) / l) by
          field_simp]
        have : 1 ≤ 2 * ((l : ℝ) - 1) / l := by
          rw [le_div_iff₀ (by linarith)]; linarith
        nlinarith
    _ = 2 * ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / l := by
        rw [Finset.mul_sum]
    _ ≤ 2 * ∑ l ∈ T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ Y), Real.log l / l := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl
          simp only [Finset.mem_filter] at hl ⊢
          exact ⟨hl.1, by omega, hl.2.2⟩
        · intro l _ _
          have : (0:ℝ) ≤ l := by positivity
          rcases Nat.eq_zero_or_pos l with h | h
          · subst h; simp
          · have : (1:ℝ) ≤ l := by exact_mod_cast h
            exact div_nonneg (Real.log_nonneg this) (by linarith)
    _ ≤ 2 * (1 + Real.log Y) ^ 2 := by
        have := sum_log_div_le T Y hY
        linarith

def frobeniusStickelbergerDetMulSigmaCube (u : ℝ) : ℝ := (Real.log u + 2) / u

lemma logAddTwoDivSelf_nonneg {u : ℝ} (hu : 1 ≤ u) : 0 ≤ frobeniusStickelbergerDetMulSigmaCube u := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  have := Real.log_nonneg hu
  positivity

lemma log_sub_le {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : Real.log v - Real.log u ≤ (v - u) / u := by
  have h := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne'] at h
  have : v / u - 1 = (v - u) / u := by field_simp
  linarith

lemma step_le (u M : ℝ) (hu : 1 ≤ u) (hM : 1 ≤ M) :
    Real.log (u + M) / (u + M) ^ 2 ≤ (frobeniusStickelbergerDetMulSigmaCube u - frobeniusStickelbergerDetMulSigmaCube (u + M)) / M := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  have hu0 : 0 < u := by linarith
  have huM : 0 < u + M := by linarith
  have ha : 0 ≤ Real.log u := Real.log_nonneg hu
  have hb := log_sub_le hu0 huM
  have hX : 0 ≤ Real.log u * u + M - Real.log (u + M) * u := by
    have : (u + M - u) / u * u = M := by field_simp; ring
    have h2 : (Real.log (u + M) - Real.log u) * u ≤ (u + M - u) / u * u :=
      mul_le_mul_of_nonneg_right hb hu0.le
    nlinarith
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  rw [div_sub_div _ _ hu0.ne' huM.ne']
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u + 2 * M) hX, mul_nonneg ha (mul_nonneg (by linarith : (0:ℝ) ≤ M) (by linarith : (0:ℝ) ≤ M)),
    mul_nonneg (by linarith : (0:ℝ) ≤ M) hu0.le, mul_pos huM huM, mul_pos hu0 huM]

lemma tele_le (u M : ℝ) (hu : 1 ≤ u) (hM : 1 ≤ M) (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.log (u + ((j : ℝ) + 1) * M) / (u + ((j : ℝ) + 1) * M) ^ 2 ≤
      (frobeniusStickelbergerDetMulSigmaCube u - frobeniusStickelbergerDetMulSigmaCube (u + (J : ℝ) * M)) / M := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hJ : 1 ≤ u + (J : ℝ) * M := by
      have : (0:ℝ) ≤ (J : ℝ) * M := by positivity
      linarith
    have hs := step_le (u + (J : ℝ) * M) M hJ hM
    have e1 : u + ((J : ℝ) + 1) * M = u + (J : ℝ) * M + M := by ring
    have e2 : u + ((J + 1 : ℕ) : ℝ) * M = u + (J : ℝ) * M + M := by push_cast; ring
    rw [e1, e2]
    have : (frobeniusStickelbergerDetMulSigmaCube u - frobeniusStickelbergerDetMulSigmaCube (u + ↑J * M)) / M + (frobeniusStickelbergerDetMulSigmaCube (u + ↑J * M) - frobeniusStickelbergerDetMulSigmaCube (u + ↑J * M + M)) / M =
        (frobeniusStickelbergerDetMulSigmaCube u - frobeniusStickelbergerDetMulSigmaCube (u + ↑J * M + M)) / M := by ring
    linarith

lemma ap_sum (S : Finset ℕ) (u0 M : ℕ) (hu : 1 ≤ u0) (hM : 1 ≤ M)
    (hS : ∀ l ∈ S, ∃ j : ℕ, l = u0 + j * M) :
    ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2 ≤ Real.log u0 / (u0 : ℝ) ^ 2 + frobeniusStickelbergerDetMulSigmaCube u0 / M := by
  classical
  set N := S.sup id with hN
  have hsub : S ⊆ (Finset.range (N + 1)).image (fun j => u0 + j * M) := by
    intro l hl
    obtain ⟨j, rfl⟩ := hS _ hl
    rw [Finset.mem_image]
    refine ⟨j, ?_, rfl⟩
    rw [Finset.mem_range]
    have h1 : u0 + j * M ≤ N := Finset.le_sup (f := id) hl
    have h2 : j ≤ j * M := Nat.le_mul_of_pos_right j hM
    omega
  have hinj : Set.InjOn (fun j => u0 + j * M) ↑(Finset.range (N + 1)) := by
    intro a _ b _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_right hM (by omega)
  have hu' : (1 : ℝ) ≤ u0 := by exact_mod_cast hu
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  calc ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2
      ≤ ∑ l ∈ (Finset.range (N + 1)).image (fun j => u0 + j * M), Real.log l / (l : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro l _ _
        have := Real.log_natCast_nonneg l
        positivity
    _ = ∑ j ∈ Finset.range (N + 1), Real.log ((u0 + j * M : ℕ) : ℝ) / ((u0 + j * M : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_image hinj]
    _ = ∑ j ∈ Finset.range N, Real.log ((u0 : ℝ) + ((j : ℝ) + 1) * M) / ((u0 : ℝ) + ((j : ℝ) + 1) * M) ^ 2
          + Real.log u0 / (u0 : ℝ) ^ 2 := by
        rw [Finset.sum_range_succ']
        push_cast
        simp
    _ ≤ (frobeniusStickelbergerDetMulSigmaCube u0 - frobeniusStickelbergerDetMulSigmaCube (u0 + (N : ℝ) * M)) / M + Real.log u0 / (u0 : ℝ) ^ 2 := by
        have := tele_le (u0 : ℝ) (M : ℝ) hu' hM' N
        linarith
    _ ≤ Real.log u0 / (u0 : ℝ) ^ 2 + frobeniusStickelbergerDetMulSigmaCube u0 / M := by
        have h0 : 0 ≤ frobeniusStickelbergerDetMulSigmaCube (u0 + (N : ℝ) * M) := logAddTwoDivSelf_nonneg (by
          have : (0:ℝ) ≤ (N : ℝ) * M := by positivity
          linarith)
        have : (frobeniusStickelbergerDetMulSigmaCube u0 - frobeniusStickelbergerDetMulSigmaCube (u0 + (N : ℝ) * M)) / M ≤ frobeniusStickelbergerDetMulSigmaCube u0 / M :=
          div_le_div_of_nonneg_right (by linarith) (by linarith)
        linarith

theorem sum_log_div_sq_le (T : Finset ℕ) :
    ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l), Real.log l / (l : ℝ) ^ 2 ≤ 2 := by
  have h := ap_sum (T.filter (fun l : ℕ => 2 ≤ l)) 1 1 le_rfl le_rfl (by
    intro l hl
    simp only [Finset.mem_filter] at hl
    exact ⟨l - 1, by omega⟩)
  have : frobeniusStickelbergerDetMulSigmaCube ((1 : ℕ) : ℝ) = 2 := by unfold frobeniusStickelbergerDetMulSigmaCube; simp
  rw [this] at h
  simpa using h

theorem sum_log_div_sq_tail (T : Finset ℕ) (A : ℝ) (hA : 2 ≤ A) :
    ∑ l ∈ T.filter (fun l : ℕ => A ≤ (l : ℝ)), Real.log l / (l : ℝ) ^ 2 ≤ 4 * (Real.log A + 2) / A := by
  set c := ⌈A⌉₊ with hc
  have hcA : A ≤ (c : ℝ) := Nat.le_ceil A
  have hcA' : (c : ℝ) < A + 1 := Nat.ceil_lt_add_one (by linarith)
  have hc2 : 2 ≤ c := by
    have : (1 : ℝ) < c := by linarith
    exact_mod_cast this
  have hu : 1 ≤ c - 1 := by omega
  have hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h := ap_sum (T.filter (fun l : ℕ => A ≤ (l : ℝ))) (c - 1) 1 hu le_rfl (by
    intro l hl
    simp only [Finset.mem_filter] at hl
    have : c ≤ l := Nat.ceil_le.mpr hl.2
    exact ⟨l - (c - 1), by omega⟩)
  rw [hcast] at h
  unfold frobeniusStickelbergerDetMulSigmaCube at h
  set u := (c : ℝ) - 1 with hu_def
  have hu1 : 1 ≤ u := by
    have : (2:ℝ) ≤ c := by exact_mod_cast hc2
    linarith
  have huA : u < A := by linarith
  have huA2 : A / 2 ≤ u := by linarith
  have hlogu : Real.log u ≤ Real.log A := Real.log_le_log (by linarith) huA.le
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hA0 : 0 < A := by linarith
  simp only [Nat.cast_one, div_one] at h
  have h1 : Real.log u / u ^ 2 ≤ Real.log u / u := by
    apply div_le_div_of_nonneg_left hlogu0 (by linarith)
    nlinarith
  have h2 : (Real.log u + 2) / u ≤ (Real.log A + 2) / (A / 2) := by
    apply div_le_div₀ (by linarith) (by linarith) (by linarith) huA2
  have h3 : Real.log u / u ≤ (Real.log A + 2) / (A / 2) := by
    apply div_le_div₀ (by linarith) (by linarith) (by linarith) huA2
  have h4 : (Real.log A + 2) / (A / 2) = 2 * (Real.log A + 2) / A := by
    field_simp
  have h5 : 4 * (Real.log A + 2) / A = 2 * (Real.log A + 2) / A + 2 * (Real.log A + 2) / A := by ring
  linarith

lemma log_ge_one_of_three {Y : ℝ} (hY : 3 ≤ Y) : 1 ≤ Real.log Y := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  norm_num at this
  linarith

lemma logsq_anti {u Y : ℝ} (hY : 3 ≤ Y) (hu : Y ≤ u) :
    Real.log u / u ^ 2 ≤ Real.log Y / Y ^ 2 := by
  have hY0 : 0 < Y := by linarith
  have hu0 : 0 < u := by linarith
  have hl := log_ge_one_of_three hY
  have hb := log_sub_le hY0 hu0
  have hd : (Real.log u - Real.log Y) * Y ≤ u - Y := by
    have := mul_le_mul_of_nonneg_right hb hY0.le
    have e : (u - Y) / Y * Y = u - Y := by field_simp
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl), mul_nonneg (sub_nonneg.mpr hu) hY0.le,
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)) (by linarith : (0:ℝ) ≤ u + Y),
    mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu)]

lemma logAddTwoDivSelf_le_of_le {u Y : ℝ} (hY : 1 ≤ Y) (hu : Y ≤ u) : frobeniusStickelbergerDetMulSigmaCube u ≤ frobeniusStickelbergerDetMulSigmaCube Y := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  have hY0 : 0 < Y := by linarith
  have hu0 : 0 < u := by linarith
  have hl := Real.log_nonneg hY
  have hb := log_sub_le hY0 hu0
  have hd : (Real.log u - Real.log Y) * Y ≤ u - Y := by
    have := mul_le_mul_of_nonneg_right hb hY0.le
    have e : (u - Y) / Y * Y = u - Y := by field_simp
    linarith
  rw [div_le_div_iff₀ hu0 hY0]
  nlinarith [mul_nonneg hl (sub_nonneg.mpr hu)]

theorem sum_log_div_sq_mod_pm_one_le (T : Finset ℕ) (M : ℕ) (Y : ℝ) (hY : 3 ≤ Y) (hYM : Y ≤ (M : ℝ) - 1) :
    ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l % M = 1 ∨ l % M = M - 1)), Real.log l / (l : ℝ) ^ 2 ≤
      2 * Real.log Y / Y ^ 2 + 2 * (Real.log Y + 2) / (Y * M) := by
  classical
  have hM4 : (4 : ℝ) ≤ M := by linarith
  have hM4n : 4 ≤ M := by exact_mod_cast hM4
  have hMpos : (0 : ℝ) < M := by linarith
  set f : ℕ → ℝ := fun l => Real.log l / (l : ℝ) ^ 2 with hf
  have fnn : ∀ l, 0 ≤ f l := by
    intro l
    have := Real.log_natCast_nonneg l
    simp only [hf]
    positivity
  have hsplit : ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ (l % M = 1 ∨ l % M = M - 1)), f l ≤
      ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = 1), f l +
      ∑ l ∈ T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = M - 1), f l := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro l _
    have := fnn l
    split_ifs <;> first | linarith | (exfalso; tauto)
  have h1 := ap_sum (T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = 1)) (M + 1) M (by omega) (by omega) (by
    intro l hl
    simp only [Finset.mem_filter] at hl
    have h := Nat.div_add_mod l M
    rw [hl.2.2] at h
    obtain ⟨q, hq⟩ : ∃ q, l / M = q + 1 := by
      rcases Nat.eq_zero_or_pos (l / M) with h0 | h0
      · rw [h0] at h; omega
      · exact ⟨l / M - 1, by omega⟩
    rw [hq] at h
    exact ⟨q, by linarith⟩)
  have h2 := ap_sum (T.filter (fun l : ℕ => 2 ≤ l ∧ l % M = M - 1)) (M - 1) M (by omega) (by omega) (by
    intro l hl
    simp only [Finset.mem_filter] at hl
    have h := Nat.div_add_mod l M
    rw [hl.2.2] at h
    exact ⟨l / M, by linarith⟩)
  have c1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  have c2 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [c1] at h1
  rw [c2] at h2
  have a1 : Real.log ((M : ℝ) + 1) / ((M : ℝ) + 1) ^ 2 ≤ Real.log Y / Y ^ 2 := logsq_anti hY (by linarith)
  have a2 : Real.log ((M : ℝ) - 1) / ((M : ℝ) - 1) ^ 2 ≤ Real.log Y / Y ^ 2 := logsq_anti hY hYM
  have b1 : frobeniusStickelbergerDetMulSigmaCube ((M : ℝ) + 1) / M ≤ frobeniusStickelbergerDetMulSigmaCube Y / M :=
    div_le_div_of_nonneg_right (logAddTwoDivSelf_le_of_le (by linarith) (by linarith)) hMpos.le
  have b2 : frobeniusStickelbergerDetMulSigmaCube ((M : ℝ) - 1) / M ≤ frobeniusStickelbergerDetMulSigmaCube Y / M :=
    div_le_div_of_nonneg_right (logAddTwoDivSelf_le_of_le (by linarith) hYM) hMpos.le
  have e : frobeniusStickelbergerDetMulSigmaCube Y / M = (Real.log Y + 2) / (Y * M) := by unfold frobeniusStickelbergerDetMulSigmaCube; rw [div_div]
  have e2 : 2 * Real.log Y / Y ^ 2 + 2 * (Real.log Y + 2) / (Y * M) =
      2 * (Real.log Y / Y ^ 2) + 2 * ((Real.log Y + 2) / (Y * M)) := by ring
  simp only [hf] at hsplit
  linarith

theorem sum_padicVal_log_le (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (n : ℕ) (hn : n ≠ 0) :
    ∑ p ∈ T, (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  classical
  have hlog : Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  have hT' : ∑ p ∈ T, (padicValNat p n : ℝ) * Real.log p =
      ∑ p ∈ T, (n.factorization p : ℝ) * Real.log p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.factorization_def n (hT p hp)]
  rw [hT', hlog]
  calc ∑ p ∈ T, (n.factorization p : ℝ) * Real.log p
      = ∑ p ∈ T ∩ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro p hp hnot
        have : p ∉ n.primeFactors := fun h => hnot (Finset.mem_inter.mpr ⟨hp, h⟩)
        rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at this
        simp [this]
    _ ≤ ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro p _ _
        have := Real.log_natCast_nonneg p
        positivity

end Formalism.MainNotions.TwistedPlaces.Sums

end

namespace Formalism.MainNotions.TwistedPlaces.Cong

lemma coprime_two_pow_of_odd (K : ℕ) (g : ℤ) (hg : Odd g) : IsCoprime ((2:ℤ) ^ K) g := by
  apply IsCoprime.pow_left
  rw [Prime.coprime_iff_not_dvd Int.prime_two, ← even_iff_two_dvd, Int.not_even_iff_odd]
  exact hg

lemma geom_sum_even_iff (x : ℤ) (hx : Odd x) (n : ℕ) :
    Even (∑ i ∈ Finset.range n, x ^ i) ↔ Even n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Int.even_add, ih, Nat.even_add_one]
    have : ¬ Even (x ^ n) := by
      rw [Int.not_even_iff_odd]; exact hx.pow
    tauto

lemma dvd_sub_one_of_pow_odd (K : ℕ) (x : ℤ) (hx : Odd x) (m : ℕ) (hm : Odd m)
    (h : (2:ℤ) ^ K ∣ x ^ m - 1) : (2:ℤ) ^ K ∣ x - 1 := by
  have hg : Odd (∑ i ∈ Finset.range m, x ^ i) := by
    rw [← Int.not_even_iff_odd, geom_sum_even_iff x hx m, Nat.not_even_iff_odd]; exact hm
  rw [← mul_geom_sum] at h
  exact (coprime_two_pow_of_odd K _ hg).dvd_of_dvd_mul_right h

lemma pm_of_pow_odd (K : ℕ) (x : ℤ) (hx : Odd x) (m : ℕ) (hm : Odd m)
    (h : (2:ℤ) ^ K ∣ x ^ m - 1 ∨ (2:ℤ) ^ K ∣ x ^ m + 1) :
    (2:ℤ) ^ K ∣ x - 1 ∨ (2:ℤ) ^ K ∣ x + 1 := by
  rcases h with h | h
  · exact Or.inl (dvd_sub_one_of_pow_odd K x hx m hm h)
  · right
    have h' : (2:ℤ) ^ K ∣ (-x) ^ m - 1 := by
      rw [hm.neg_pow]
      have e : -x ^ m - 1 = -(x ^ m + 1) := by ring
      rw [e, dvd_neg]; exact h
    have := dvd_sub_one_of_pow_odd K (-x) hx.neg m hm h'
    have e : -x - 1 = -(x + 1) := by ring
    rwa [e, dvd_neg] at this

lemma pm_of_sq (K : ℕ) (y : ℤ) (hy : Odd y)
    (h : (2:ℤ) ^ K ∣ y ^ 2 - 1 ∨ (2:ℤ) ^ K ∣ y ^ 2 + 1) :
    (2:ℤ) ^ (K - 1) ∣ y - 1 ∨ (2:ℤ) ^ (K - 1) ∣ y + 1 := by
  obtain ⟨b, rfl⟩ := hy
  rcases K with _ | _ | k
  · simp
  · simp
  simp only [Nat.add_sub_cancel]
  have e4 : (2:ℤ) ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
  rw [e4] at h
  rcases h with h | h
  · have e : (2 * b + 1) ^ 2 - 1 = 4 * (b * (b + 1)) := by ring
    rw [e] at h
    have h' := (mul_dvd_mul_iff_left (by norm_num : (4:ℤ) ≠ 0)).mp h
    rcases Int.even_or_odd b with hb | hb
    · left
      have hb1 : Odd (b + 1) := hb.add_one
      have : (2:ℤ) ^ k ∣ b := (coprime_two_pow_of_odd k _ hb1).dvd_of_dvd_mul_right h'
      have e2 : 2 * b + 1 - 1 = 2 * b := by ring
      rw [e2, pow_succ, mul_comm _ (2:ℤ)]
      exact mul_dvd_mul_left 2 this
    · right
      have : (2:ℤ) ^ k ∣ b + 1 := (coprime_two_pow_of_odd k _ hb).dvd_of_dvd_mul_left h'
      have e2 : 2 * b + 1 + 1 = 2 * (b + 1) := by ring
      rw [e2, pow_succ, mul_comm _ (2:ℤ)]
      exact mul_dvd_mul_left 2 this
  · exfalso
    have e : (2 * b + 1) ^ 2 + 1 = 4 * (b * (b + 1)) + 2 := by ring
    rw [e] at h
    have h4 : (4:ℤ) ∣ 4 * (b * (b + 1)) + 2 := dvd_trans ⟨2 ^ k, rfl⟩ h
    generalize b * (b + 1) = t at h4
    omega

lemma pm_of_two_pow (a : ℕ) : ∀ (K : ℕ) (x : ℤ), Odd x →
    ((2:ℤ) ^ K ∣ x ^ (2 ^ a) - 1 ∨ (2:ℤ) ^ K ∣ x ^ (2 ^ a) + 1) →
    ((2:ℤ) ^ (K - a) ∣ x - 1 ∨ (2:ℤ) ^ (K - a) ∣ x + 1) := by
  induction a with
  | zero => intro K x _ h; simpa using h
  | succ a ih =>
    intro K x hx h
    have h2 : (2:ℤ) ^ K ∣ (x ^ (2 ^ a)) ^ 2 - 1 ∨ (2:ℤ) ^ K ∣ (x ^ (2 ^ a)) ^ 2 + 1 := by
      rwa [← pow_mul, ← pow_succ]
    have := ih (K - 1) x hx (pm_of_sq K _ hx.pow h2)
    rwa [Nat.sub_sub, Nat.add_comm 1 a] at this

lemma pm_int (K : ℕ) (x : ℤ) (hx : Odd x) (o : ℕ) (ho : 0 < o)
    (h : (2:ℤ) ^ K ∣ x ^ o - 1 ∨ (2:ℤ) ^ K ∣ x ^ o + 1) :
    (2:ℤ) ^ (K - padicValNat 2 o) ∣ x - 1 ∨ (2:ℤ) ^ (K - padicValNat 2 o) ∣ x + 1 := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd ho.ne'
  have hv : padicValNat 2 (2 ^ a * m) = a := by
    rw [padicValNat.mul (by positivity) hm.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]), add_zero]
  rw [hv]
  apply pm_of_two_pow a K x hx
  rw [pow_mul] at h
  exact pm_of_pow_odd K _ hx.pow m hm h

theorem ordPM_nonempty (K l : ℕ) (hl : Odd l) :
    {o : ℕ | 0 < o ∧ ((l : ZMod (2 ^ K)) ^ o = 1 ∨ (l : ZMod (2 ^ K)) ^ o = -1)}.Nonempty := by
  have hc : Nat.Coprime l (2 ^ K) := by
    apply Nat.Coprime.pow_right
    exact Nat.coprime_two_right.mpr hl
  refine ⟨Nat.totient (2 ^ K), Nat.totient_pos.mpr (by positivity), Or.inl ?_⟩
  have h1 := Nat.ModEq.pow_totient hc
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
  push_cast at h2
  exact h2

theorem pm_one_of_pow (K l o : ℕ) (hl : Odd l) (ho : 0 < o)
    (h : (l : ZMod (2 ^ K)) ^ o = 1 ∨ (l : ZMod (2 ^ K)) ^ o = -1) :
    l % 2 ^ (K - padicValNat 2 o) = 1 ∨ l % 2 ^ (K - padicValNat 2 o) = 2 ^ (K - padicValNat 2 o) - 1 := by
  have hlz : Odd (l : ℤ) := by exact_mod_cast hl
  have hint : (2:ℤ) ^ K ∣ (l:ℤ) ^ o - 1 ∨ (2:ℤ) ^ K ∣ (l:ℤ) ^ o + 1 := by
    rcases h with h | h
    · left
      have h0 : (((l:ℤ) ^ o - 1 : ℤ) : ZMod (2 ^ K)) = 0 := by push_cast; rw [h]; ring
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ K)).mp h0
      exact_mod_cast this
    · right
      have h0 : (((l:ℤ) ^ o + 1 : ℤ) : ZMod (2 ^ K)) = 0 := by push_cast; rw [h]; ring
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ K)).mp h0
      exact_mod_cast this
  have key := pm_int K (l:ℤ) hlz o ho hint
  generalize K - padicValNat 2 o = s at key ⊢
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; right; simp [Nat.mod_one]
  have hN : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hl1 : 1 ≤ l := hl.pos
  rcases key with h1 | h1
  · left
    have h2 : 2 ^ s ∣ l - 1 := by
      have : ((2 ^ s : ℕ) : ℤ) ∣ ((l - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hl1]; push_cast; exact h1
      exact Int.natCast_dvd_natCast.mp this
    have h3 := (Nat.modEq_iff_dvd' hl1).mpr h2
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega)] at h3
    exact h3.symm
  · right
    have h2 : 2 ^ s ∣ l + 1 := by exact_mod_cast h1
    have hr := Nat.mod_lt l (by omega : 0 < 2 ^ s)
    have h3 : (l % 2 ^ s + 1) % 2 ^ s = 0 := by
      rw [Nat.mod_add_mod]; exact Nat.mod_eq_zero_of_dvd h2
    generalize l % 2 ^ s = r at hr h3 ⊢
    generalize 2 ^ s = N at hr h3 hN ⊢
    by_contra hne
    have hlt : r + 1 < N := by omega
    rw [Nat.mod_eq_of_lt hlt] at h3
    omega

theorem two_pow_padicVal_le (o : ℕ) (ho : 0 < o) : 2 ^ padicValNat 2 o ≤ o := by
  exact Nat.le_of_dvd ho pow_padicValNat_dvd

end Formalism.MainNotions.TwistedPlaces.Cong

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces.Asym

open Real

open Asymptotics Filter

end Formalism.MainNotions.TwistedPlaces.Asym

end
