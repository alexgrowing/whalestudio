import Formalism.EllipticTorsion.Statement

open PowerSeries

noncomputable section

namespace Formalism.ELL.PadicLogarithmSubstitution

open Formalism.G Formalism.ELL

section Integral

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem integralMv_one {σ : Type*} : IntegralMv (1 : MvPowerSeries σ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem integralMv_mul {σ : Type*} {f g : MvPowerSeries σ K} (hf : IntegralMv f)
    (hg : IntegralMv g) : IntegralMv (f * g) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem integralMv_pow {σ : Type*} {f : MvPowerSeries σ K} (hf : IntegralMv f) (n : ℕ) :
    IntegralMv (f ^ n) := by
  induction n with
  | zero => simpa using (integralMv_one (K := K) (σ := σ))
  | succ n ih => rw [pow_succ]; exact integralMv_mul ih hf

theorem norm_finsum_le_one {f : ℕ → K} (h : ∀ n, ‖f n‖ ≤ 1) : ‖∑ᶠ n, f n‖ ≤ 1 := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => h i)
  · rw [finsum_of_infinite_support hs]; simp

theorem integralMv_subst {σ : Type*} {a : PowerSeries K} (ha : IntegralPS a)
    {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0) (hf : IntegralMv f) :
    IntegralMv (a.subst f) := by
  intro d
  rw [PowerSeries.coeff_subst (HasSubst.of_constantCoeff_zero hf0)]
  refine norm_finsum_le_one (fun n => ?_)
  rw [smul_eq_mul, norm_mul]
  exact mul_le_one₀ (ha n) (norm_nonneg _) (integralMv_pow hf n d)

end Integral

section LogId

variable {K : Type*} [Field K] [CharZero K]

def geometricSignedSeries (K : Type*) [Field K] [CharZero K] : PowerSeries K :=
  mk fun n => algebraMap ℚ K ((-1 : ℚ) ^ n)

theorem geomAlt_mul : geometricSignedSeries K * (1 + X) = 1 := by
  ext n
  rw [mul_add, mul_one, map_add, mul_comm]
  rcases n with _ | m
  · simp [geometricSignedSeries]
  · rw [coeff_succ_X_mul]
    simp only [geometricSignedSeries, coeff_mk, coeff_one]
    rw [← map_add]
    have : ((-1 : ℚ) ^ (m + 1) + (-1) ^ m) = 0 := by ring
    simp [this]

theorem log_subst_eq_smul (c : K) (B : PowerSeries K) (hB0 : constantCoeff B = 1)
    (hBd : (1 + X) * derivative K B = c • B) :
    (log K).subst (B - 1) = c • log K := by
  have h0 : constantCoeff (B - 1) = 0 := by simp [hB0]
  have hS : HasSubst (B - 1) := HasSubst.of_constantCoeff_zero' h0
  have hone : (1 + X : PowerSeries K).subst (B - 1) = B := by
    rw [subst_add hS, subst_X hS, ← coe_substAlgHom hS, map_one]; ring
  have hGB : (geometricSignedSeries K).subst (B - 1) * B = 1 := by
    have hm := subst_mul hS (geometricSignedSeries K) (1 + X)
    rw [geomAlt_mul, hone, ← coe_substAlgHom hS, map_one] at hm
    rw [← coe_substAlgHom hS, ← hm]
  have hD : derivative K ((log K).subst (B - 1)) = derivative K (c • log K) := by
    have hX : (1 + X : PowerSeries K) ≠ 0 := by
      intro h
      have := congrArg constantCoeff h
      simp at this
    refine mul_right_cancel₀ hX ?_
    rw [derivative_subst hS, deriv_log, Derivation.map_smul, deriv_log]
    change (geometricSignedSeries K).subst (B - 1) * derivative K (B - 1) * (1 + X) =
      c • geometricSignedSeries K * (1 + X)
    rw [map_sub, derivative_one, sub_zero, mul_assoc, mul_comm (derivative K B), hBd,
      mul_smul_comm, hGB, smul_mul_assoc, geomAlt_mul]
  refine derivative.ext hD ?_
  rw [show constantCoeff (c • log K) = 0 by simp]
  exact constantCoeff_subst_eq_zero h0 _ constantCoeff_log

end LogId

section Binom

variable (p : ℕ) [Fact p.Prime] (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]

def phi : ℤ_[p] →+* K := (algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom

def bser (b : ℤ_[p]) : PowerSeries K := mk fun n => phi p K (Ring.choose b n)

theorem choose_rec (b : ℤ_[p]) (n : ℕ) :
    ((n + 1 : ℕ) : ℤ_[p]) * Ring.choose b (n + 1) = (b - n) * Ring.choose b n := by
  have h := Ring.choose_smul_choose b (Nat.le_succ n)
  rw [Nat.choose_succ_self_right, show n.succ - n = 1 by omega, Ring.choose_one_right,
    nsmul_eq_mul] at h
  rw [mul_comm (b - (n : ℤ_[p]))]
  exact h

theorem bser_constantCoeff (b : ℤ_[p]) : constantCoeff (bser p K b) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, bser, coeff_mk, Ring.choose_zero_right, map_one]

theorem bser_deriv (b : ℤ_[p]) :
    (1 + X) * derivative K (bser p K b) = phi p K b • bser p K b := by
  ext n
  have hr := congrArg (phi p K) (choose_rec p b n)
  simp only [map_mul, map_sub, map_natCast] at hr
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_smul]
  rcases n with _ | m
  · simp only [bser, coeff_mk, coeff_zero_X_mul, smul_eq_mul] at hr ⊢
    push_cast at hr ⊢
    linear_combination hr
  · rw [coeff_succ_X_mul, coeff_derivative]
    simp only [bser, coeff_mk, smul_eq_mul] at hr ⊢
    push_cast at hr ⊢
    linear_combination hr

theorem norm_phi_le (z : ℤ_[p]) : ‖phi p K z‖ ≤ 1 := by
  rw [phi, RingHom.comp_apply, norm_algebraMap']
  exact PadicInt.norm_le_one z

theorem integralPS_bser_sub_one [IsUltrametricDist K] (b : ℤ_[p]) :
    IntegralPS (bser p K b - 1) := by
  intro n
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [bser, coeff_mk]; exact norm_phi_le p K _
  · rw [norm_neg, coeff_one]; split_ifs <;> simp

end Binom

end PadicLogarithmSubstitution

open PadicLogarithmSubstitution in
theorem N_padic_integer_smul : Formalism.ELL.NZpSmul := by
  intro p _ K _ _ _ _ σ G hG b
  obtain ⟨f, hf0, hfi, rfl⟩ := hG
  have hB0 := bser_constantCoeff p K b
  have h0 : constantCoeff (bser p K b - 1) = 0 := by simp [hB0]
  have hS : HasSubst (bser p K b - 1) := HasSubst.of_constantCoeff_zero' h0
  have hf : HasSubst f := HasSubst.of_constantCoeff_zero hf0
  have hc : algebraMap ℚ_[p] K (b : ℚ_[p]) = phi p K b := rfl
  refine ⟨(bser p K b - 1).subst f, constantCoeff_subst_eq_zero hf0 _ h0,
    integralMv_subst (integralPS_bser_sub_one p K b) hf0 hfi, ?_⟩
  unfold logOnePlus
  rw [← subst_comp_subst_apply hS hf, log_subst_eq_smul _ _ hB0 (bser_deriv p K b),
    subst_smul hf, hc]

end Formalism.ELL
