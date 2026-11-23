import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBoundOfIsBigO

open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.CuspDecay

theorem b1 : B1 := by
  intro k N _ χ f a hf
  obtain ⟨h0, ⟨C₂, hC₂⟩, ⟨D, hD⟩⟩ := coeff_and_decay f a hf.exp
  obtain ⟨C₁, hC₁⟩ := CuspFormClass.exists_bound f
  refine ⟨h0, |C₁| + |C₂| + |D|, fun z ↦ ?_, fun n ↦ ?_, fun z hz ↦ ?_⟩
  · have hy : 0 < z.im := z.im_pos
    have h1 := hC₁ z
    have he : ((k : ℤ) : ℝ) / 2 = (k : ℝ) / 2 := by push_cast; ring
    rw [he, div_eq_mul_inv, ← Real.rpow_neg hy.le] at h1
    have hp : 0 ≤ z.im ^ (-(k : ℝ) / 2) := Real.rpow_nonneg hy.le _
    have hg : -(k : ℝ) / 2 = -((k : ℝ) / 2) := by ring
    rw [hg] at hp ⊢
    calc ‖f z‖ ≤ C₁ * z.im ^ (-((k : ℝ) / 2)) := h1
      _ ≤ (|C₁| + |C₂| + |D|) * z.im ^ (-((k : ℝ) / 2)) := by
        apply mul_le_mul_of_nonneg_right _ hp
        linarith [le_abs_self C₁, abs_nonneg C₂, abs_nonneg D]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [h0, norm_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have h2 := hC₂ n hn
      have he : ((k : ℤ) : ℝ) / 2 = (k : ℝ) / 2 := by push_cast; ring
      rw [he] at h2
      refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      linarith [le_abs_self C₂, abs_nonneg C₁, abs_nonneg D]
  · refine (hD z hz).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    linarith [le_abs_self D, abs_nonneg C₁, abs_nonneg C₂]

end GlobalTheory.CompanionTheory.CuspDecay
