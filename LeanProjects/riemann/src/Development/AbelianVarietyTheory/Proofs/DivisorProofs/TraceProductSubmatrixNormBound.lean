import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
open Matrix GlobalTheory.MatDeriv
open scoped Topology

namespace GlobalTheory

theorem trace_mul_submatrix_norm_le {m : ℕ} (k : Fin (m + 1)) (P : Matrix (Fin k) (Fin k) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) (b g : ℝ) (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hP : ∀ y, ‖P *ᵥ y‖ ≤ b * ‖y‖) (hX : ∀ x, ‖X *ᵥ x‖ ≤ g * ‖x‖) :
    ‖(P * X.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
      (Fin.castLE (Nat.le_of_lt_succ k.isLt))).trace‖ ≤ m * (b * g) := by
  set c := Fin.castLE (Nat.le_of_lt_succ k.isLt) with hc
  set Y := X.submatrix c c with hY
  have hcol : ∀ j : Fin k, ‖Y *ᵥ Pi.single j 1‖ ≤ g := by
    intro j
    have h1 : ‖X *ᵥ Pi.single (c j) (1 : ℂ)‖ ≤ g := by
      refine (hX _).trans ?_
      have : ‖(Pi.single (c j) (1 : ℂ) : Fin m → ℂ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
        by_cases h : i = c j
        · subst h; simp
        · simp [Pi.single_apply, h]
      nlinarith
    refine (pi_norm_le_iff_of_nonneg hg).2 fun i => ?_
    have : (Y *ᵥ Pi.single j 1) i = (X *ᵥ Pi.single (c j) (1 : ℂ)) (c i) := by
      simp [hY, mulVec_single]
    rw [this]
    exact (norm_le_pi_norm _ _).trans h1
  have hdiag : ∀ j : Fin k, ‖(P * Y) j j‖ ≤ b * g := by
    intro j
    have : (P * Y) j j = (P *ᵥ (Y *ᵥ Pi.single j 1)) j := by
      rw [mulVec_single_one]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [this]
    exact (norm_le_pi_norm _ _).trans ((hP _).trans (mul_le_mul_of_nonneg_left (hcol j) hb))
  have hk : (k : ℕ) ≤ m := Nat.le_of_lt_succ k.isLt
  calc ‖(P * Y).trace‖ = ‖∑ j, (P * Y) j j‖ := rfl
    _ ≤ ∑ j : Fin k, ‖(P * Y) j j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin k, b * g := Finset.sum_le_sum fun j _ => hdiag j
    _ = (k : ℝ) * (b * g) := by simp
    _ ≤ m * (b * g) := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (mul_nonneg hb hg)

end GlobalTheory
