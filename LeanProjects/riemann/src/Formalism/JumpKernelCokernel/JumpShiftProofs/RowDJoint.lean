import Formalism.JumpKernelCokernel.LemmaDJoint
import Formalism.JumpKernelCokernel.JumpShiftProofs.ThickB
import Formalism.JumpKernelCokernel.JumpShiftProofs.ExpRowD

namespace Formalism.KernelCokernelLengths.RowDegreeJointLemmas

lemma aR_nonneg (ℓ : ℕ) (hℓ : 11 ≤ ℓ) (H : ℕ) : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H := by
  unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
  have hl : (1:ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have t1 : 0 ≤ (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (sq_nonneg _)
  have t2 : 0 ≤ Real.logb (ℓ : ℝ) (2 * (H : ℝ)) := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · simp [h0]
    · have : (1:ℝ) ≤ H := by exact_mod_cast h0
      exact Real.logb_nonneg hl (by linarith)
  linarith

end Formalism.KernelCokernelLengths.RowDegreeJointLemmas

theorem Formalism.KernelCokernelLengths.row_degree_joint_form : Formalism.KernelCokernelLengths.RowDJoint := by
  refine ⟨1 / 100, by norm_num, 1000, ?_⟩
  intro ℓ hℓ b η S t bi h s₁ E e₂ hb hη hS ht h1 h2 h3
  intro η' a hs₁ hE he₂
  have hℓR : (11:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hbR : (1000:ℝ) ≤ b := by exact_mod_cast hb
  have h1R : (b:ℝ) ≤ bi + t + 1 := by exact_mod_cast h1
  have h2R : (bi:ℝ) + S ≤ h := by exact_mod_cast h2
  have h3R : (h:ℝ) ≤ b + η + t + S + 1 := by exact_mod_cast h3
  have hη' : (η' : ℝ) = η + t + 1 := by
    show ((η + t + 1 : ℕ) : ℝ) = _
    push_cast
    ring
  have hη0 : (0:ℝ) ≤ η := Nat.cast_nonneg _
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have hS0 : (0:ℝ) ≤ S := Nat.cast_nonneg _
  have hA : 2 * η' ≤ h := by
    have : (2 * (η' : ℝ)) ≤ h := by rw [hη']; linarith
    exact_mod_cast this
  have hB : h ≤ 2 * bi := by
    have : (h : ℝ) ≤ 2 * bi := by linarith
    exact_mod_cast this
  have haR := Formalism.KernelCokernelLengths.RowDegreeJointLemmas.aR_nonneg ℓ hℓ (h + η')
  have ha : (a : ℝ) ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + η') + 1 := (Nat.ceil_lt_add_one haR).le
  have hC : 2 * a + η' + 1 ≤ bi := by
    have hHR : ((h + η' : ℕ) : ℝ) ≤ 1.05 * b + 2 := by push_cast; rw [hη']; linarith
    have hH1 : (1:ℝ) ≤ ((h + η' : ℕ) : ℝ) := by push_cast; rw [hη']; linarith
    have hfrac : (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ 21 / 100 := by
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have he5 : (100:ℝ) ≤ Real.exp 5 := by
      have e1 := Real.exp_one_gt_d9
      have e2 : (2.7:ℝ) ^ 5 < Real.exp 1 ^ 5 := pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
      rw [← Real.exp_nat_mul] at e2
      norm_num at e2
      linarith
    have hlog : ∀ y : ℝ, 0 < y → Real.log y ≤ y / 100 + 4 := by
      intro y hy
      have h5 := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 5))
      rw [Real.log_div hy.ne' (Real.exp_pos 5).ne', Real.log_exp] at h5
      have : y / Real.exp 5 ≤ y / 100 := div_le_div_of_nonneg_left hy.le (by norm_num) he5
      linarith
    have hl11 : (2:ℝ) < Real.log ℓ := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have e1 := Real.exp_one_lt_d9
      have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      nlinarith [Real.exp_pos 1]
    have hlam : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam ℓ (h + η') ≤ ((h + η' : ℕ) : ℝ) / 100 + 3 := by
      unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
      have hy : (0:ℝ) < 2 * ((h + η' : ℕ) : ℝ) := by linarith
      have hlg := hlog _ hy
      have hlg0 : 0 ≤ Real.log (2 * ((h + η' : ℕ) : ℝ)) := Real.log_nonneg (by linarith)
      rw [Real.logb]
      have hdd : Real.log (2 * ((h + η' : ℕ) : ℝ)) / Real.log ℓ ≤ Real.log (2 * ((h + η' : ℕ) : ℝ)) / 2 :=
        div_le_div_of_nonneg_left hlg0 (by norm_num) hl11.le
      linarith
    have haR2 : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + η') ≤ 0.22 * ((h + η' : ℕ) : ℝ) + 6 := by
      unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR
      have : ((h + η' : ℕ) : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤
          ((h + η' : ℕ) : ℝ) * (21 / 100) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)
      linarith
    have : (2 * (a : ℝ) + η' + 1) ≤ bi := by rw [hη'] at *; linarith
    exact_mod_cast this
  refine ⟨⟨hA, hB, hC⟩, ?_⟩
  exact Formalism.KernelCokernelLengths.row_degree_exponent ℓ hℓ h η' S bi a s₁ E e₂ hA (by omega) ha hs₁ hE he₂
