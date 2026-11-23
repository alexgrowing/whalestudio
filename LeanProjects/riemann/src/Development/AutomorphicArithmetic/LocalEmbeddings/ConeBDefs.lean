import Mathlib

noncomputable section

namespace FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

open MeasureTheory

variable {ι : Type} [Fintype ι]

def ec (x : ι → ℂ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (((∑ w, x w).re : ℝ) : ℂ))

def FT (f : (ι → ℂ) → ℂ) (y : ι → ℂ) : ℂ := ∫ s, f s * ec (s * y)

def wt (κ : ι → ℤ) (e : ℕ) (s : ι → ℂ) : ℂ := ∏ w, (s w / (‖s w‖ : ℂ)) ^ κ w * (‖s w‖ : ℂ) ^ (2 * e)

def nm (y : ι → ℂ) : ℝ := ∏ w, ‖y w‖ ^ 2

def dwt (κ : ι → ℤ) (e : ℕ) (y : ι → ℂ) : ℂ := (wt κ e y * (nm y : ℂ))⁻¹

def pr {n : ℕ} (v η : Fin n × ι → ℂ) : ι → ℂ := fun w => ∑ i, v (i, w) * η (i, w)

def sc {n : ℕ} (y : ι → ℂ) (η : Fin n × ι → ℂ) : Fin n × ι → ℂ := fun p => y p.2 * η p

theorem norm_ec (x : ι → ℂ) : ‖ec x‖ = 1 := by
  rw [ec, Complex.norm_exp]
  simp

theorem continuous_ec : Continuous (ec : (ι → ℂ) → ℂ) := by
  unfold ec
  fun_prop

theorem wt_mul (κ : ι → ℤ) (e : ℕ) (s t : ι → ℂ) : wt κ e (s * t) = wt κ e s * wt κ e t := by
  simp only [wt, Pi.mul_apply, norm_mul, Complex.ofReal_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [mul_div_mul_comm, mul_zpow, mul_pow]
  ring

theorem nm_mul (s t : ι → ℂ) : nm (s * t) = nm s * nm t := by
  simp only [nm, Pi.mul_apply, norm_mul, mul_pow, Finset.prod_mul_distrib]

theorem dwt_mul (κ : ι → ℤ) (e : ℕ) (s t : ι → ℂ) : dwt κ e (s * t) = dwt κ e s * dwt κ e t := by
  simp only [dwt, wt_mul, nm_mul, Complex.ofReal_mul, mul_inv]
  ring

theorem nm_pos {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) : 0 < nm y :=
  Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hy w)) 2

theorem wt_ne_zero (κ : ι → ℤ) (e : ℕ) {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) : wt κ e y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ => by
    have h : (‖y w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 (hy w)
    exact mul_ne_zero (zpow_ne_zero _ (div_ne_zero (hy w) h)) (pow_ne_zero _ h)

theorem measurable_wt (κ : ι → ℤ) (e : ℕ) : Measurable (wt κ e) := by
  unfold wt
  refine Finset.measurable_prod _ fun w _ => ?_
  have h : Measurable fun s : ι → ℂ => (‖s w‖ : ℂ) := Complex.measurable_ofReal.comp (measurable_pi_apply w).norm
  exact (((measurable_pi_apply w).div h).pow_const _).mul (h.pow_const _)

theorem continuous_nm : Continuous (nm : (ι → ℂ) → ℝ) := by
  unfold nm
  fun_prop

theorem measurable_dwt (κ : ι → ℤ) (e : ℕ) : Measurable (dwt κ e) :=
  ((measurable_wt κ e).mul (Complex.measurable_ofReal.comp continuous_nm.measurable)).inv

theorem norm_wt_le (κ : ι → ℤ) (e : ℕ) (s : ι → ℂ) : ‖wt κ e s‖ ≤ (1 + ‖s‖) ^ (2 * e * Fintype.card ι) := by
  rw [wt, norm_prod, pow_mul, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun w _ => ?_
  rw [norm_mul, norm_zpow, norm_pow, norm_div, Complex.norm_real, norm_norm]
  have h1 : (‖s w‖ / ‖s w‖) ^ κ w ≤ 1 := by
    by_cases h : ‖s w‖ = 0
    · rw [h, div_zero]
      by_cases hk : κ w = 0
      · simp [hk]
      · simp [zero_zpow _ hk]
    · rw [div_self h, one_zpow]
  have h2 : ‖s w‖ ^ (2 * e) ≤ (1 + ‖s‖) ^ (2 * e) :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_le_pi_norm s w]) _
  calc _ ≤ 1 * (1 + ‖s‖) ^ (2 * e) := mul_le_mul h1 h2 (by positivity) zero_le_one
    _ = _ := one_mul _

omit [Fintype ι] in

theorem dense_ne_zero : Dense {s : ι → ℂ | ∀ w, s w ≠ 0} := by
  have h := dense_pi (ι := ι) (α := fun _ => ℂ) (s := fun _ => ({0}ᶜ : Set ℂ)) Set.univ fun _ _ => dense_compl_singleton 0
  convert h using 1
  ext s
  simp [Set.mem_pi]

end FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

end
