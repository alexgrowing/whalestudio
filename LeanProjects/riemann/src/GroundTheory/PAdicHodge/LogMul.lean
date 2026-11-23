import Mathlib
import GroundTheory.PAdicHodge.BdRSeries
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open PowerSeries

section Formal

theorem exp_subst_log : (exp ℚ).subst (log ℚ) = (1 + X : ℚ⟦X⟧) := by
  have hS : HasSubst (log ℚ) := HasSubst.log
  set F : ℚ⟦X⟧ := (exp ℚ).subst (log ℚ) with hF
  set G : ℚ⟦X⟧ := mk (fun n => algebraMap ℚ ℚ ((-1) ^ n)) with hG
  have h1 : (1 + X : ℚ⟦X⟧) * G = 1 := one_add_X_mul_geom
  have hF' : d⁄dX ℚ F = F * G := by
    rw [hF, derivative_subst hS, derivative_exp, deriv_log]
  have hG' : d⁄dX ℚ G = -(G * G) := by
    have h := congrArg (d⁄dX ℚ) h1
    rw [Derivation.leibniz, derivative_one, map_add, derivative_one, derivative_X, zero_add,
      smul_eq_mul, smul_eq_mul, mul_one] at h
    calc d⁄dX ℚ G = G * ((1 + X) * d⁄dX ℚ G) := by
          rw [← mul_assoc, mul_comm G, h1, one_mul]
      _ = -(G * G) := by
          rw [show (1 + X) * d⁄dX ℚ G = -G from eq_neg_of_add_eq_zero_left h]
          ring
  have hc : constantCoeff F = 1 := by
    have h0 : MvPowerSeries.constantCoeff (log ℚ) = 0 := constantCoeff_log
    have hz := constantCoeff_subst_eq_zero h0 (exp ℚ - 1) (by simp [constantCoeff_exp])
    have hsub : (exp ℚ - 1 : ℚ⟦X⟧).subst (log ℚ) = F - 1 := by
      rw [hF, ← coe_substAlgHom hS, map_sub, map_one]
    rw [hsub, map_sub, map_one, sub_eq_zero] at hz
    exact hz
  have hGc : constantCoeff G = 1 := by
    rw [hG, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp
  have hH : F * G = 1 := by
    apply derivative.ext
    · rw [Derivation.leibniz, hF', hG', derivative_one, smul_eq_mul, smul_eq_mul]
      ring
    · rw [map_mul, hc, hGc, map_one, mul_one]
  calc F = F * ((1 + X) * G) := by rw [h1, mul_one]
    _ = (F * G) * (1 + X) := by ring
    _ = 1 + X := by rw [hH, one_mul]

end Formal

section Nilpotent

variable {S : Type*} [CommRing S] [Algebra ℚ S]

theorem truncEval_pow_eq_zero {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧}
    (hg : constantCoeff g = 0) : (truncEval s hs g) ^ n = 0 := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.2 hg
  rw [← map_pow, mul_pow, map_mul, map_pow, truncEval_X, hs, zero_mul]

theorem truncEval_subst {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧} (hg : constantCoeff g = 0)
    (f : ℚ⟦X⟧) :
    truncEval s hs (f.subst g) = truncEval (truncEval s hs g) (truncEval_pow_eq_zero hs hg) f := by
  have hS := HasSubst.of_constantCoeff_zero' hg
  have key := truncEval_unique ((truncEval s hs).comp (substAlgHom hS)) (truncEval s hs g)
    (truncEval_pow_eq_zero hs hg) (by rw [AlgHom.comp_apply, coe_substAlgHom, subst_X hS])
  rw [← key, AlgHom.comp_apply, coe_substAlgHom]

theorem truncEval_exp {n : ℕ} {s : S} (hs : s ^ n = 0) :
    truncEval s hs (exp ℚ) = IsNilpotent.exp s := by
  rw [truncEval_eq_sum, IsNilpotent.exp_eq_sum hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_exp, Algebra.smul_def, one_div]
  simp

theorem isNilpotent_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent (truncEval s hs (log ℚ)) :=
  ⟨n, truncEval_pow_eq_zero hs constantCoeff_log⟩

theorem exp_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent.exp (truncEval s hs (log ℚ)) = 1 + s := by
  rw [← truncEval_exp (truncEval_pow_eq_zero hs constantCoeff_log),
    ← truncEval_subst hs (g := log ℚ) constantCoeff_log,
    exp_subst_log, map_add, map_one, truncEval_X]

theorem eq_zero_of_exp_eq_one {c : S} (hc : IsNilpotent c) (h : IsNilpotent.exp c = 1) : c = 0 := by
  obtain ⟨k, hk⟩ := hc
  set w : S := ∑ i ∈ Finset.range k, ((i + 1).factorial : ℚ)⁻¹ • c ^ i with hw
  have hexp : IsNilpotent.exp c = 1 + c * w := by
    rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_succ k) hk), Finset.sum_range_succ',
      hw, Finset.mul_sum]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, pow_succ, mul_comm c]
  have hw1 : IsUnit w := by
    rcases k with _ | k
    · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hk.symm)
      exact isUnit_of_subsingleton w
    · have hsplit : w = 1 + c * ∑ i ∈ Finset.range k, ((i + 2).factorial : ℚ)⁻¹ • c ^ i := by
        rw [hw, Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, zero_add, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, pow_succ, mul_comm c]
      rw [hsplit]
      exact IsNilpotent.isUnit_one_add ⟨k + 1, by rw [mul_pow, hk, zero_mul]⟩
  have h0 : c * w = 0 := by
    have := hexp.symm.trans h
    rwa [add_eq_left] at this
  simpa using (hw1.mul_left_eq_zero).1 h0

theorem eq_of_exp_eq {a b : S} (ha : IsNilpotent a) (hb : IsNilpotent b)
    (h : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  have hnb : IsNilpotent (-b) := hb.neg
  have h1 : IsNilpotent.exp (a + -b) = 1 := by
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) ha hnb, h,
      IsNilpotent.exp_mul_exp_neg_self hb]
  have h2 := eq_zero_of_exp_eq_one (Commute.isNilpotent_add (Commute.all _ _) ha hnb) h1
  rw [← sub_eq_add_neg, sub_eq_zero] at h2
  exact h2

theorem truncEval_log_mul {l m n : ℕ} {x y z : S} (hx : x ^ l = 0) (hy : y ^ m = 0)
    (hz : z ^ n = 0) (hxyz : 1 + z = (1 + x) * (1 + y)) :
    truncEval z hz (log ℚ) = truncEval x hx (log ℚ) + truncEval y hy (log ℚ) := by
  have hnx := isNilpotent_truncEval_log hx
  have hny := isNilpotent_truncEval_log hy
  apply eq_of_exp_eq (isNilpotent_truncEval_log hz) (Commute.isNilpotent_add (Commute.all _ _) hnx hny)
  rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hnx hny, exp_truncEval_log,
    exp_truncEval_log, exp_truncEval_log, hxyz]

end Nilpotent

section Complete

variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]

theorem mk_seriesEval_eq_truncEval {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (seriesEval I z hz f) =
      truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n) f :=
  IsAdicComplete.mk_liftAlgHom I
    (fun n => truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n))
    (fun hle => factorₐ_comp_truncEval I hz hle) n f

theorem logOnePlus_mul {x y z : B} (hx : x ∈ I) (hy : y ∈ I) (hz : z ∈ I)
    (hxyz : 1 + z = (1 + x) * (1 + y)) :
    logOnePlus I z hz = logOnePlus I x hx + logOnePlus I y hy := by
  refine eq_of_forall_sub_mem_pow I fun n => ?_
  rw [← Ideal.Quotient.eq, map_add, logOnePlus, logOnePlus, logOnePlus,
    mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval]
  exact truncEval_log_mul _ _ _ (by rw [← map_one (Ideal.Quotient.mk (I ^ n)), ← map_add, hxyz,
    map_mul, map_add, map_add, map_one])

end Complete

end GroundTheory.PAdicHodge
