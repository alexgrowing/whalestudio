import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.Growth

open Matrix Finset

noncomputable section

namespace Formalism.MainNotions.GrowthW.ExpUp

open Formalism.MainNotions.GrowthW

variable {m : ℕ}

theorem pow_entry_zero {X : Matrix (Fin m) (Fin m) ℂ} (hX : SUpper X) :
    ∀ (p : ℕ) (i j : Fin m), (j : ℕ) < i + p → (X ^ p) i j = 0 := by
  intro p
  induction p with
  | zero =>
    intro i j hij
    rw [pow_zero, Matrix.one_apply_ne]
    intro h
    subst h
    omega
  | succ p ih =>
    intro i j hij
    rw [pow_succ X p, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : (l : ℕ) < i + p
    · rw [ih i l hl, zero_mul]
    · rw [hX l j (Fin.le_iff_val_le_val.mpr (by omega)), mul_zero]

open scoped Matrix.Norms.Operator in
theorem exp_entry_eq {X : Matrix (Fin m) (Fin m) ℂ} (hX : SUpper X) (i j : Fin m) :
    (NormedSpace.exp X) i j = ∑ n ∈ range (m + 1 + 1), ((n.factorial : ℂ)⁻¹) * (X ^ n) i j := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X
  let L : Matrix (Fin m) (Fin m) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h1 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) ((NormedSpace.exp X) i j) :=
    L.hasSum h
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j)
      (∑ n ∈ range (m + 1 + 1), ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [Finset.mem_range] at hn
    have hj := j.isLt
    rw [pow_entry_zero hX n i j (by omega), mul_zero]
  exact h1.unique h2

theorem exp_entry_peel {X : Matrix (Fin m) (Fin m) ℂ} (hX : SUpper X) (i j : Fin m) :
    (NormedSpace.exp X) i j = ∑ q ∈ range m, ((Nat.factorial (q + 1 + 1) : ℂ)⁻¹) * (X ^ (q + 1 + 1)) i j
      + X i j + (1 : Matrix (Fin m) (Fin m) ℂ) i j := by
  rw [exp_entry_eq hX, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_mul, pow_one,
    pow_zero]

theorem exp_diag {X : Matrix (Fin m) (Fin m) ℂ} (hX : SUpper X) (i : Fin m) :
    (NormedSpace.exp X) i i = 1 := by
  rw [exp_entry_peel hX, Finset.sum_eq_zero (fun q _ => by
    rw [pow_entry_zero hX (q + 1 + 1) i i (by omega), mul_zero]), hX i i le_rfl, Matrix.one_apply_eq,
    zero_add, zero_add]

theorem entry_le_hsN (A : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : ‖A i j‖ ≤ hsN A := by
  rw [Complex.norm_def, hsN]
  apply Real.sqrt_le_sqrt
  calc Complex.normSq (A i j) ≤ ∑ j', Complex.normSq (A i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (A i j'))
          (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (A i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (A i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem hsN_le (A : Matrix (Fin m) (Fin m) ℂ) {b : ℝ} (hb : 0 ≤ b) (h : ∀ i j, ‖A i j‖ ≤ b) :
    hsN A ≤ m * b := by
  unfold hsN
  have key : ∑ i, ∑ j, Complex.normSq (A i j) ≤ ((m : ℝ) * b) ^ 2 := by
    calc ∑ i, ∑ j, Complex.normSq (A i j) ≤ ∑ _i : Fin m, ∑ _j : Fin m, b ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [Complex.normSq_eq_norm_sq]
            nlinarith [mul_le_mul (h i j) (h i j) (norm_nonneg _) hb, norm_nonneg (A i j)]
      _ = ((m : ℝ) * b) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) ≤ Real.sqrt (((m : ℝ) * b) ^ 2) := Real.sqrt_le_sqrt key
    _ = m * b := Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) hb)

theorem one_le_hsN_exp (hm : 0 < m) {X : Matrix (Fin m) (Fin m) ℂ} (hX : SUpper X) :
    1 ≤ hsN (NormedSpace.exp X) := by
  have h := entry_le_hsN (NormedSpace.exp X) ⟨0, hm⟩ ⟨0, hm⟩
  rw [exp_diag hX, norm_one] at h
  exact h

theorem pow_entry_bound {X : Matrix (Fin m) (Fin m) ℂ} (hX : SUpper X) {h : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hB : ∀ i j : Fin m, (j : ℕ) < i + h → ‖X i j‖ ≤ b) :
    ∀ p : ℕ, ∀ i j : Fin m, (j : ℕ) < i + h + p → ‖(X ^ (p + 1)) i j‖ ≤ (m : ℝ) ^ p * b ^ (p + 1) := by
  intro p
  induction p with
  | zero =>
    intro i j hij
    simpa using hB i j (by omega)
  | succ p ih =>
    intro i j hij
    rw [pow_succ X (p + 1), Matrix.mul_apply]
    have hR0 : 0 ≤ (m : ℝ) ^ p * b ^ (p + 1) := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hb _)
    have hR : 0 ≤ (m : ℝ) ^ p * b ^ (p + 1) * b := mul_nonneg hR0 hb
    have hterm : ∀ l : Fin m, ‖(X ^ (p + 1)) i l * X l j‖ ≤ (m : ℝ) ^ p * b ^ (p + 1) * b := by
      intro l
      by_cases h1 : (j : ℕ) ≤ l
      · rw [hX l j (Fin.le_iff_val_le_val.mpr h1), mul_zero, norm_zero]
        exact hR
      by_cases h2 : (l : ℕ) < i + (p + 1)
      · rw [pow_entry_zero hX (p + 1) i l h2, zero_mul, norm_zero]
        exact hR
      rw [norm_mul]
      exact mul_le_mul (ih i l (by omega)) (hB l j (by omega)) (norm_nonneg _) hR0
    calc ‖∑ l, (X ^ (p + 1)) i l * X l j‖ ≤ ∑ l, ‖(X ^ (p + 1)) i l * X l j‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin m, (m : ℝ) ^ p * b ^ (p + 1) * b := Finset.sum_le_sum (fun l _ => hterm l)
      _ = (m : ℝ) ^ (p + 1) * b ^ (p + 1 + 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

theorem entry_le_sum {X : Matrix (Fin m) (Fin m) ℂ} (hX : SUpper X) (i j : Fin m) :
    ‖X i j‖ ≤ ‖(NormedSpace.exp X) i j‖ + 1 + ∑ q ∈ range m, ‖(X ^ (q + 1 + 1)) i j‖ := by
  have hp := exp_entry_peel hX i j
  have h1 : ‖(1 : Matrix (Fin m) (Fin m) ℂ) i j‖ ≤ 1 := by
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have h2 : ‖∑ q ∈ range m, ((Nat.factorial (q + 1 + 1) : ℂ)⁻¹) * (X ^ (q + 1 + 1)) i j‖ ≤
      ∑ q ∈ range m, ‖(X ^ (q + 1 + 1)) i j‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_mul]
    have hf : ‖((Nat.factorial (q + 1 + 1) : ℂ)⁻¹)‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_natCast]
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
    calc _ ≤ 1 * ‖(X ^ (q + 1 + 1)) i j‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg _)
      _ = _ := one_mul _
  have hx : X i j = NormedSpace.exp X i j -
      (∑ q ∈ range m, ((Nat.factorial (q + 1 + 1) : ℂ)⁻¹) * (X ^ (q + 1 + 1)) i j) -
      (1 : Matrix (Fin m) (Fin m) ℂ) i j := by
    rw [hp]
    ring
  rw [hx]
  have t1 := norm_sub_le (NormedSpace.exp X i j -
      (∑ q ∈ range m, ((Nat.factorial (q + 1 + 1) : ℂ)⁻¹) * (X ^ (q + 1 + 1)) i j))
    ((1 : Matrix (Fin m) (Fin m) ℂ) i j)
  have t2 := norm_sub_le (NormedSpace.exp X i j)
    (∑ q ∈ range m, ((Nat.factorial (q + 1 + 1) : ℂ)⁻¹) * (X ^ (q + 1 + 1)) i j)
  linarith

theorem real_step {N A : ℝ} {e m : ℕ} (hN : 1 ≤ N) (hA : 0 ≤ A) (he : 1 ≤ e) :
    N + 1 + (m : ℝ) * ((m : ℝ) ^ m * (1 + A * N ^ e) ^ (m + 1)) ≤
      (2 + (m : ℝ) ^ (m + 1) * (1 + A) ^ (m + 1)) * N ^ (e * (m + 1)) := by
  have hN0 : 0 ≤ N := by linarith
  have hNe : 1 ≤ N ^ e := one_le_pow₀ hN
  have h1 : 1 + A * N ^ e ≤ (1 + A) * N ^ e := by
    have : (1 + A) * N ^ e = N ^ e + A * N ^ e := by ring
    rw [this]; linarith
  have h0 : 0 ≤ 1 + A * N ^ e := by have := mul_nonneg hA (pow_nonneg hN0 e); linarith
  have h2 : (1 + A * N ^ e) ^ (m + 1) ≤ (1 + A) ^ (m + 1) * N ^ (e * (m + 1)) := by
    calc (1 + A * N ^ e) ^ (m + 1) ≤ ((1 + A) * N ^ e) ^ (m + 1) := pow_le_pow_left₀ h0 h1 _
      _ = (1 + A) ^ (m + 1) * N ^ (e * (m + 1)) := by rw [mul_pow, ← pow_mul]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ (m + 1) := pow_nonneg (Nat.cast_nonneg _) _
  have key : (m : ℝ) * ((m : ℝ) ^ m * (1 + A * N ^ e) ^ (m + 1)) ≤
      (m : ℝ) ^ (m + 1) * ((1 + A) ^ (m + 1) * N ^ (e * (m + 1))) := by
    calc (m : ℝ) * ((m : ℝ) ^ m * (1 + A * N ^ e) ^ (m + 1))
        = (m : ℝ) ^ (m + 1) * (1 + A * N ^ e) ^ (m + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hm0
  have hpos : e * (m + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hNE : N ≤ N ^ (e * (m + 1)) := le_self_pow₀ hN hpos
  have h1E : 1 ≤ N ^ (e * (m + 1)) := one_le_pow₀ hN
  have eq : (2 + (m : ℝ) ^ (m + 1) * (1 + A) ^ (m + 1)) * N ^ (e * (m + 1)) =
      2 * N ^ (e * (m + 1)) + (m : ℝ) ^ (m + 1) * ((1 + A) ^ (m + 1) * N ^ (e * (m + 1))) := by ring
  rw [eq]
  linarith

theorem height_bound (hm : 0 < m) : ∀ h : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ X : Matrix (Fin m) (Fin m) ℂ, SUpper X →
    ∀ i j : Fin m, (j : ℕ) < i + h → ‖X i j‖ ≤ A * hsN (NormedSpace.exp X) ^ ((m + 1) ^ h) := by
  intro h
  induction h with
  | zero =>
    refine ⟨0, le_rfl, fun X hX i j hij => ?_⟩
    rw [hX i j (Fin.le_iff_val_le_val.2 (by omega)), norm_zero, zero_mul]
  | succ h ih =>
    obtain ⟨A, hA, hAX⟩ := ih
    refine ⟨2 + (m : ℝ) ^ (m + 1) * (1 + A) ^ (m + 1),
      add_nonneg zero_le_two (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (by linarith) _)),
      fun X hX i j hij => ?_⟩
    have hN : 1 ≤ hsN (NormedSpace.exp X) := one_le_hsN_exp hm hX
    have hb : 0 ≤ A * hsN (NormedSpace.exp X) ^ ((m + 1) ^ h) :=
      mul_nonneg hA (pow_nonneg (by linarith) _)
    have hP := pow_entry_bound hX (h := h) hb (hAX X hX)
    have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.2 hm
    have hsum : ∑ q ∈ range m, ‖(X ^ (q + 1 + 1)) i j‖ ≤
        (m : ℝ) * ((m : ℝ) ^ m * (1 + A * hsN (NormedSpace.exp X) ^ ((m + 1) ^ h)) ^ (m + 1)) := by
      calc ∑ q ∈ range m, ‖(X ^ (q + 1 + 1)) i j‖
          ≤ ∑ _q ∈ range m, (m : ℝ) ^ m * (1 + A * hsN (NormedSpace.exp X) ^ ((m + 1) ^ h)) ^ (m + 1) := by
            refine Finset.sum_le_sum fun q hq => ?_
            have hq' : q < m := Finset.mem_range.1 hq
            refine (hP (q + 1) i j (by omega)).trans ?_
            exact mul_le_mul (pow_le_pow_right₀ hm1 (by omega))
              ((pow_le_pow_left₀ hb (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega)))
              (pow_nonneg hb _) (pow_nonneg (Nat.cast_nonneg _) _)
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hE := entry_le_hsN (NormedSpace.exp X) i j
    have hmain := entry_le_sum hX i j
    have he : (m + 1) ^ (h + 1) = (m + 1) ^ h * (m + 1) := pow_succ _ _
    rw [he]
    have hst := real_step (m := m) hN hA (Nat.one_le_pow _ _ (by omega) : 1 ≤ (m + 1) ^ h)
    linarith

theorem expUpper_pos (m : ℕ) (hm : 0 < m) : ∃ C D : ℝ, 0 < D ∧ ∀ X : Matrix (Fin m) (Fin m) ℂ, SUpper X →
    1 + hsN X ≤ C * hsN (NormedSpace.exp X) ^ D := by
  obtain ⟨A, hA, hH⟩ := height_bound hm m
  refine ⟨1 + m * A, (((m + 1) ^ m : ℕ) : ℝ), by positivity, fun X hX => ?_⟩
  have hE : 1 ≤ hsN (NormedSpace.exp X) := one_le_hsN_exp hm hX
  have hEp : 1 ≤ hsN (NormedSpace.exp X) ^ ((m + 1) ^ m) := one_le_pow₀ hE
  have hX' : hsN X ≤ m * (A * hsN (NormedSpace.exp X) ^ ((m + 1) ^ m)) :=
    hsN_le X (mul_nonneg hA (pow_nonneg (by linarith) _)) (fun i j => hH X hX i j (by
      have := j.isLt
      omega))
  rw [Real.rpow_natCast]
  have hq : (1 + (m : ℝ) * A) * hsN (NormedSpace.exp X) ^ ((m + 1) ^ m) =
      hsN (NormedSpace.exp X) ^ ((m + 1) ^ m) + (m : ℝ) * (A * hsN (NormedSpace.exp X) ^ ((m + 1) ^ m)) := by
    ring
  rw [hq]
  linarith

end Formalism.MainNotions.GrowthW.ExpUp

namespace Formalism.MainNotions.GrowthW

theorem expUpper : ExpUpper := fun m hm => ExpUp.expUpper_pos m hm

end Formalism.MainNotions.GrowthW
