import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl

noncomputable section

namespace GlobalTheory.ExpImage.TaylorEps

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.MemLoc
open Polynomial
open scoped Formalism.Per

section poly
variable (K : Type) [Field K] [CharZero K]

def logT (M : ℕ) : K[X] := ∑ k ∈ Finset.range M, C ((-1) ^ k * ((k + 1 : ℕ) : K)⁻¹) * X ^ (k + 1)

theorem logT_deriv (M : ℕ) : (1 + X) * derivative (logT K M) = 1 - (-X) ^ M := by
  induction M with
  | zero => simp [logT]
  | succ M ih =>
    have h : ((M + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast M.succ_ne_zero
    have e : derivative (C ((-1) ^ M * ((M + 1 : ℕ) : K)⁻¹) * X ^ (M + 1) : K[X]) = (-X) ^ M := by
      rw [derivative_C_mul, derivative_X_pow, ← mul_assoc, ← C_mul, mul_assoc, inv_mul_cancel₀ h,
        mul_one, neg_pow (X : K[X])]
      simp
    rw [logT, Finset.sum_range_succ, derivative_add, e, mul_add, ← logT, ih]
    ring

theorem X_dvd_logT (M : ℕ) : X ∣ logT K M :=
  Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (dvd_pow_self _ k.succ_ne_zero) _

theorem expT_deriv (L : K[X]) (M : ℕ) :
    derivative (∑ j ∈ Finset.range (M + 1), C ((j.factorial : K)⁻¹) * L ^ j) =
      derivative L * ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h : ((M + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast M.succ_ne_zero
    have h' : ((M.factorial : ℕ) : K) ≠ 0 := by exact_mod_cast M.factorial_ne_zero
    have e : (((M + 1).factorial : ℕ) : K)⁻¹ * ((M + 1 : ℕ) : K) = ((M.factorial : ℕ) : K)⁻¹ := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp
    rw [Finset.sum_range_succ, derivative_add, ih, Finset.sum_range_succ _ M, derivative_C_mul,
      derivative_pow, ← e, C_mul]
    simp only [Nat.add_sub_cancel]
    ring

theorem exp_log_dvd (M : ℕ) :
    X ^ M ∣ 1 + X - ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * logT K M ^ j := by
  rcases M with _ | M
  · simp
  set L := logT K (M + 1) with hL
  set D := 1 + X - ∑ j ∈ Finset.range (M + 1), C ((j.factorial : K)⁻¹) * L ^ j with hD
  have h1 : X ^ M ∣ X * derivative D + derivative D - D := by
    have e : X * derivative D + derivative D - D = C ((M.factorial : K)⁻¹) * L ^ M +
        (-X) ^ (M + 1) * ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j := by
      have := logT_deriv K (M + 1)
      rw [← hL] at this
      rw [hD, derivative_sub, expT_deriv, Finset.sum_range_succ]
      simp only [derivative_add, derivative_one, derivative_X]
      linear_combination (-∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j) * this
    rw [e]
    refine dvd_add (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (X_dvd_logT K _) M) _)
      (Dvd.dvd.mul_right ?_ _)
    rw [neg_pow, pow_succ X]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  have h0 : D.coeff 0 = 0 := by
    have hL0 : L.eval 0 = 0 := by
      rw [← coeff_zero_eq_eval_zero]; exact X_dvd_iff.1 (X_dvd_logT K _)
    rw [coeff_zero_eq_eval_zero, hD, Finset.sum_range_succ']
    simp [eval_finset_sum, hL0]
  rw [X_pow_dvd_iff] at h1 ⊢
  intro d
  induction d with
  | zero => exact fun _ => h0
  | succ d ih =>
    intro hd
    have a := ih (by omega)
    have b := h1 d (by omega)
    have c : (X * derivative D).coeff d = 0 := by
      rcases d with _ | d
      · simp
      · rw [coeff_X_mul, coeff_derivative, a, zero_mul]
    rw [coeff_sub, coeff_add, c, a, coeff_derivative, zero_add, sub_zero] at b
    exact (mul_eq_zero.1 b).resolve_right (by exact_mod_cast d.succ_ne_zero)

end poly

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem aeval_mem {x : P.R.BdR} (hx : x ∈ FilB P 0) (f : ℚ_[l][X]) : aeval x f ∈ FilB P 0 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial]
    exact qB_mul_mem a (by simpa using FilB_pow hx n)

theorem io_eq (T : LocTied l P AI) (a : Ainf l) :
    T.eD (io AI a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := GlobalTheory.ThetaTie.eD_ιA T a

theorem mu_mem (T : LocTied l P AI) : io AI (mu AI.ε) ∈ FilB P 1 := by
  obtain ⟨y, hy, e⟩ := T.t
  have h : io AI (mu AI.ε) - tD P ∈ FilB P ((2 : ℕ) : ℤ) := by
    refine (GlobalTheory.ThetaTie.fil_nat T 2 _).2 ⟨_, GlobalTheory.ThetaTie.log_mu (GlobalTheory.ThetaTie.isEps AI) hy, ?_⟩
    rw [map_sub, map_sub, e, io_eq]
  have := add_mem (FilB_anti (a := 1) (by norm_num) h) (tD_mem (P := P))
  simpa using this

theorem t_sub_log (T : LocTied l P AI) (M : ℕ) :
    tD P - aeval (io AI (mu AI.ε)) (logT ℚ_[l] M) ∈ FilB P (M : ℤ) := by
  obtain ⟨y, hy, e⟩ := T.t
  have h : (M.factorial : P.R.BdR) * tD P - ∑ k ∈ Finset.range M,
      (-1) ^ k * ((M.factorial / (k + 1) : ℕ) : P.R.BdR) * io AI (mu AI.ε) ^ (k + 1) ∈
        FilB P (M : ℤ) := by
    refine (GlobalTheory.ThetaTie.fil_nat T M _).2 ⟨(M.factorial : Per.BdRp l) * y -
      algebraMap (Per.AinfP l) (Per.BdRp l) (∑ k ∈ Finset.range M,
        (-1) ^ k * ((M.factorial / (k + 1) : ℕ) : Per.AinfP l) *
          (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm AI.ε - 1)) ^ (k + 1)), ?_, ?_⟩
    · refine (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l M _).2 ?_
      rw [map_sub, GlobalTheory.ThetaTie.ev_alg, map_mul, map_natCast,
        GlobalTheory.CrisIncl.factorial_mul_ev l _ y (GlobalTheory.ThetaTie.isEps AI).1 hy M, sub_self]
    · simp only [map_sub, map_mul, map_natCast, map_sum, map_pow, map_neg, e, io_eq]
      simp only [map_one]
      simp only [aDp, mu, RingHom.comp_apply, map_sub, map_one]
  have h0 : ((M.factorial : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast M.factorial_ne_zero
  have := qB_mul_mem ((M.factorial : ℕ) : ℚ_[l])⁻¹ h
  convert this using 1
  rw [mul_sub, ← mul_assoc, ← map_natCast (qB P), ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul,
    logT, map_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ∣ M.factorial := Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk)
  have h1 : ((k + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast k.succ_ne_zero
  have e1 : ((k + 1 : ℕ) : ℚ_[l])⁻¹ =
      ((M.factorial : ℕ) : ℚ_[l])⁻¹ * ((M.factorial / (k + 1) : ℕ) : ℚ_[l]) := by
    rw [Nat.cast_div hk' h1]
    field_simp
  rw [map_mul, aeval_C, map_pow, aeval_X, e1]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

theorem eps_sub_exp (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (M : ℕ) : io AI (WittVector.teichmuller l AI.ε) -
      ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j ∈ FilB P (M : ℤ) := by
  have hm := mu_mem T
  have hm0 := FilB_anti (a := 0) (by norm_num) hm
  have hL := aeval_mem hm0 (logT ℚ_[l] M)
  have ht := FilB_anti (a := 0) (by norm_num) (tD_mem (P := P))
  have hd := t_sub_log T M
  obtain ⟨Q, hQ⟩ := exp_log_dvd ℚ_[l] M
  have h1 := congrArg (aeval (io AI (mu AI.ε))) hQ
  simp only [map_sub, map_add, map_one, aeval_X, map_sum, map_mul, aeval_C, map_pow] at h1
  have h2 := FilB_zero_mul (aeval_mem hm0 Q) (FilB_pow hm M)
  rw [mul_one, mul_comm, ← h1] at h2
  generalize aeval (io AI (mu AI.ε)) (logT ℚ_[l] M) = L at hL hd h2
  have h3 : ∀ j : ℕ, tD P ^ j - L ^ j ∈ FilB P (M : ℤ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := add_mem (FilB_zero_mul ht ih)
        (FilB_zero_mul (x := L ^ j) (by simpa using FilB_pow hL j) hd)
      convert this using 1
      ring
  have h4 := Submodule.sum_mem (FilB P (M : ℤ)) (t := Finset.range M)
    fun j _ => qB_mul_mem ((j.factorial : ℚ_[l])⁻¹) (h3 j)
  have e : io AI (WittVector.teichmuller l AI.ε) = 1 + io AI (mu AI.ε) := by
    rw [mu, map_sub, map_one, add_sub_cancel]
  have := sub_mem h2 h4
  rw [e]
  convert this using 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end GlobalTheory.ExpImage.TaylorEps
