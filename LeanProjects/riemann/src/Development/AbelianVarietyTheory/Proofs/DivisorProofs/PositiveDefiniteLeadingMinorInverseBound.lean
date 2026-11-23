import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
open Matrix GlobalTheory.MatDeriv
open scoped Topology

set_option autoImplicit false

namespace GlobalTheory

theorem leadingBlock_inv_mulVec_norm_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (k : Fin (m + 1)) (c : ℝ)
    (hc : 0 < c)
    (hdet : IsUnit (M.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
      (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det)
    (hcoer : ∀ v : Fin m → ℂ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ M *ᵥ v).re)
    (z : Fin k → ℂ) :
    ‖(M.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
      (Fin.castLE (Nat.le_of_lt_succ k.isLt)))⁻¹ *ᵥ z‖ ≤ m / c * ‖z‖ := by
  set e : Fin k → Fin m := Fin.castLE (Nat.le_of_lt_succ k.isLt) with he
  set A := M.submatrix e e with hA
  set y := A⁻¹ *ᵥ z with hy
  have hAy : A *ᵥ y = z := by
    rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have he_inj : Function.Injective e := Fin.castLE_injective _
  set v : Fin m → ℂ := Function.extend e y 0 with hvdef
  have hv_e : ∀ a, v (e a) = y a := fun a => he_inj.extend_apply y 0 a
  have hv_out : ∀ x ∉ Set.range e, v x = 0 := by
    intro x hx
    rw [hvdef, Function.extend_apply' _ _ _ (by simpa [Set.mem_range] using hx)]
    rfl
  have hMv : ∀ i, (M *ᵥ v) i = ∑ a, M i (e a) * y a := by
    intro i
    simp only [mulVec, dotProduct]
    symm
    apply Fintype.sum_of_injective e he_inj
    · intro x hx; simp [hv_out x hx]
    · intro a; simp [hv_e]
  have key : star v ⬝ᵥ M *ᵥ v = star y ⬝ᵥ A *ᵥ y := by
    simp only [dotProduct]
    symm
    apply Fintype.sum_of_injective e he_inj
    · intro x hx; simp [hv_out x hx]
    · intro a
      rw [Pi.star_apply, Pi.star_apply, hv_e, hMv]
      simp [hA, mulVec, dotProduct]
  have hyv : ‖y‖ ≤ ‖v‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
    rw [← hv_e a]; exact norm_le_pi_norm v (e a)
  have h1 : c * ‖y‖ ^ 2 ≤ (star y ⬝ᵥ z).re := by
    calc c * ‖y‖ ^ 2 ≤ c * ‖v‖ ^ 2 := by gcongr
      _ ≤ _ := hcoer v
      _ = _ := by rw [key, hAy]
  have h2 : (star y ⬝ᵥ z).re ≤ (k : ℕ) * (‖y‖ * ‖z‖) := by
    calc (star y ⬝ᵥ z).re ≤ ‖star y ⬝ᵥ z‖ := Complex.re_le_norm _
      _ ≤ ∑ i, ‖star y i * z i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin k, ‖y‖ * ‖z‖ := by
          gcongr with i
          rw [norm_mul, Pi.star_apply, norm_star]
          exact mul_le_mul (norm_le_pi_norm y i) (norm_le_pi_norm z i) (norm_nonneg _) (norm_nonneg _)
      _ = (k : ℕ) * (‖y‖ * ‖z‖) := by simp
  have hkm : ((k : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ k.isLt
  have h3 : c * ‖y‖ ^ 2 ≤ m * (‖y‖ * ‖z‖) :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_right hkm (by positivity)))
  rcases (norm_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    have h4 : ‖y‖ * (‖y‖ * c) ≤ ‖y‖ * (m * ‖z‖) := by nlinarith
    exact le_of_mul_le_mul_left h4 hpos

end GlobalTheory
