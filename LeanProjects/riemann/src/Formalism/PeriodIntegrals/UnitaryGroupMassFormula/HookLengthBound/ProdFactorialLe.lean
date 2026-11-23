import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DiagonalMonomialFactorial

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

theorem sum_rev_eq (N : ℕ) : ∑ i : Fin N, (N - 1 - (i : ℕ)) = N * (N - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
  have h := Finset.sum_range_reflect (fun i => i) N
  rw [h, Finset.sum_range_id]

theorem factorial_add_le (a k B : ℕ) (h : a + k ≤ B) : (a + k).factorial ≤ a.factorial * B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    rw [← add_assoc, Nat.factorial_succ, pow_succ]
    calc (a + k + 1) * (a + k).factorial ≤ B * (a.factorial * B ^ k) :=
          Nat.mul_le_mul (by omega) ih'
      _ = a.factorial * (B ^ k * B) := by ring

theorem prod_factorial_le (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ) (hν : Antitone ν) :
    ∏ i : Fin N, (ν i + (N - 1 - i)).factorial ≤
      (∏ i, (ν i).factorial) * (ν ⟨0, hN⟩ + N) ^ (N * (N - 1) / 2) := by
  have hB : ∀ i : Fin N, ν i + (N - 1 - i) ≤ ν ⟨0, hN⟩ + N := fun i => by
    have := hν (show (⟨0, hN⟩ : Fin N) ≤ i from Nat.zero_le _)
    omega
  calc ∏ i : Fin N, (ν i + (N - 1 - i)).factorial
      ≤ ∏ i : Fin N, ((ν i).factorial * (ν ⟨0, hN⟩ + N) ^ (N - 1 - (i : ℕ))) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => factorial_add_le _ _ _ (hB i)
    _ = (∏ i, (ν i).factorial) * (ν ⟨0, hN⟩ + N) ^ (N * (N - 1) / 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_rev_eq]

theorem hook_bound : HookBoundOf := by
  unfold HookBoundOf PI.HookBound
  intro hH N hN ν hν
  have h1 := PI.HookLower.one_le_cNu ν hν
  refine ⟨h1, ?_⟩
  have hD : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ) :=
    Finset.prod_pos fun l _ => by exact_mod_cast (ν l).factorial_pos
  unfold PI.cNu at h1 ⊢
  have hF0r : (0 : ℝ) ≤ (fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℝ) := by
    have := (one_le_div hD).1 h1
    linarith
  have hF0 : (0 : ℚ) ≤ fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by exact_mod_cast hF0r
  have hP : (1 : ℚ) ≤ ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((ν i - ν j + (j - i) : ℕ) : ℚ) := by
    calc (1 : ℚ) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (1 : ℚ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
          Finset.prod_le_prod (fun _ _ => zero_le_one) fun j hj => by
            have hij' : i < j := Finset.mem_Ioi.1 hj
            have hij : (i : ℕ) < j := hij'
            exact_mod_cast (show 1 ≤ ν i - ν j + (j - i) by omega)
  have hQ := hH N ν hν
  have hFQ : fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) ≤
      ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℚ) := by
    rw [← hQ]
    exact le_mul_of_one_le_right hF0 hP
  have hFQr : (fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℝ) ≤
      ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℝ) := by exact_mod_cast hFQ
  have hle : (∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℝ)) ≤
      (∏ i, ((ν i).factorial : ℝ)) * ((ν ⟨0, hN⟩ : ℝ) + N) ^ (N * (N - 1) / 2) := by
    exact_mod_cast prod_factorial_le N hN ν hν
  rw [div_le_iff₀ hD]
  linarith

end PI.HookSteps
