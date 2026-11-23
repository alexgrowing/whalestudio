import Mathlib

open UpperHalfPlane hiding I
open Complex Filter Asymptotics CongruenceSubgroup ModularFormClass
open scoped Real MatrixGroups Modular

namespace GlobalTheory.CompanionTheory.CuspDecay

theorem exists_bound_of_isBigO {a : ℕ → ℂ} {e : ℝ}
    (h : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ e) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ e := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hC
  refine ⟨|C| + ∑ m ∈ Finset.range n₀, ‖a m‖ / (m : ℝ) ^ e, fun n hn ↦ ?_⟩
  have hpos : 0 < (n : ℝ) ^ e := Real.rpow_pos_of_pos (by exact_mod_cast hn) e
  have hS : ∀ m ∈ Finset.range n₀, 0 ≤ ‖a m‖ / (m : ℝ) ^ e := fun m _ ↦
    div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) e)
  have hS0 := Finset.sum_nonneg hS
  rcases lt_or_ge n n₀ with h1 | h1
  · have h2 := Finset.single_le_sum hS (Finset.mem_range.mpr h1)
    have h3 : ‖a n‖ = ‖a n‖ / (n : ℝ) ^ e * (n : ℝ) ^ e := by field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C]) hpos.le
  · have h2 := hn₀ n h1
    rw [Real.norm_of_nonneg hpos.le] at h2
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ hpos.le)
    linarith [le_abs_self C]

theorem exists_exp_bound {f : ℍ → ℂ} {e C : ℝ}
    (hO : f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im))
    (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ e) :
    ∃ D : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ D * Real.exp (-τ.im) := by
  obtain ⟨D, hD⟩ := hO.bound
  rw [atImInfty, eventually_comap, eventually_atTop] at hD
  obtain ⟨A₀, hA⟩ := hD
  set A := max A₀ 1 with hAdef
  have hA1 : 1 ≤ A := le_max_right _ _
  refine ⟨|D| + |C| * A ^ |e| * Real.exp A, fun τ hτ ↦ ?_⟩
  have hy : 0 < τ.im := τ.im_pos
  have hE : 0 < Real.exp (-τ.im) := Real.exp_pos _
  have hAe : 0 ≤ |C| * A ^ |e| * Real.exp A := by positivity
  rcases le_total A τ.im with h1 | h1
  · have h2 := hA τ.im ((le_max_left _ _).trans h1) τ rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    have h3 : Real.exp (-2 * π * τ.im) ≤ Real.exp (-τ.im) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three]
    calc ‖f τ‖ ≤ D * Real.exp (-2 * π * τ.im) := h2
      _ ≤ |D| * Real.exp (-2 * π * τ.im) :=
        mul_le_mul_of_nonneg_right (le_abs_self D) (Real.exp_pos _).le
      _ ≤ |D| * Real.exp (-τ.im) := mul_le_mul_of_nonneg_left h3 (abs_nonneg D)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE.le
  · have h2 : (τ.im ^ e)⁻¹ ≤ A ^ |e| := by
      rw [← Real.rpow_neg hy.le]
      calc τ.im ^ (-e) ≤ τ.im ^ |e| := Real.rpow_le_rpow_of_exponent_le hτ (neg_le_abs e)
        _ ≤ A ^ |e| := Real.rpow_le_rpow hy.le h1 (abs_nonneg e)
    have h3 : 1 ≤ Real.exp A * Real.exp (-τ.im) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have hAp : 0 ≤ A ^ |e| := by positivity
    calc ‖f τ‖ ≤ C / τ.im ^ e := hC τ
      _ = C * (τ.im ^ e)⁻¹ := div_eq_mul_inv _ _
      _ ≤ |C| * (τ.im ^ e)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr (by positivity))
      _ ≤ |C| * A ^ |e| := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      _ ≤ |C| * A ^ |e| * (Real.exp A * Real.exp (-τ.im)) :=
        le_mul_of_one_le_right (by positivity) h3
      _ = |C| * A ^ |e| * Real.exp A * Real.exp (-τ.im) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg D]) hE.le

theorem coeff_and_decay {N : ℕ} [NeZero N] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (a : ℕ → ℂ)
    (ha : ∀ τ : ℍ, HasSum (fun n : ℕ ↦ a n * cexp (2 * π * I * n * τ)) (f τ)) :
    a 0 = 0 ∧ (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2)) ∧
      ∃ D : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ D * Real.exp (-τ.im) := by
  have hΓ : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  have hcoef : ∀ m, a m = (qExpansion 1 f).coeff m := by
    refine ModularFormClass.qExpansion_coeff_unique (Γ := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
      (k := k) one_pos hΓ fun τ ↦ ?_
    convert ha τ using 3 with n
    rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoef]
    exact CuspFormClass.qExpansion_coeff_zero (Γ := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
      (k := k) f one_pos hΓ
  · have h := CuspFormClass.qExpansion_isBigO (Γ := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
      (k := k) f
    have hw : (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty = 1 := by simp
    rw [hw] at h
    have ha' : a = fun n ↦ (qExpansion 1 f).coeff n := funext hcoef
    rw [← ha'] at h
    exact exists_bound_of_isBigO h
  · obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (Γ := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
      (k := k) f
    have hO := CuspFormClass.exp_decay_atImInfty (Γ := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
      (k := k) (h := 1) f one_pos hΓ
    simp only [Nat.cast_one, div_one] at hO
    exact exists_exp_bound (by simpa using hO) hC

end GlobalTheory.CompanionTheory.CuspDecay
