import Mathlib

noncomputable section

open Polynomial

namespace GroundTheory.Global

section MatrixJacobi

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

def matrixGeomSeries (M : Matrix n n R) : Matrix n n (PowerSeries R) :=
  Matrix.of fun i j => PowerSeries.mk fun k => (M ^ k) i j

theorem coeff_map_C_mul_matrixGeomSeries (M : Matrix n n R) (k : ℕ) (i j : n) :
    PowerSeries.coeff k ((M.map PowerSeries.C * matrixGeomSeries M) i j) = (M ^ (k + 1)) i j := by
  rw [pow_succ', Matrix.mul_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [matrixGeomSeries, PowerSeries.coeff_C_mul]

theorem one_sub_X_smul_mul_matrixGeomSeries (M : Matrix n n R) :
    (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C) * matrixGeomSeries M = 1 := by
  ext i j k
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, map_sub]
  rcases k with _ | k
  · simp [matrixGeomSeries, Matrix.one_apply]
  · rw [PowerSeries.coeff_succ_X_mul, coeff_map_C_mul_matrixGeomSeries]
    by_cases h : i = j <;> simp [matrixGeomSeries, Matrix.one_apply, h]

theorem trace_matrixGeomSeries_mul (M : Matrix n n R) :
    (matrixGeomSeries M * M.map PowerSeries.C).trace =
      PowerSeries.mk fun k => (M ^ (k + 1)).trace := by
  ext k
  rw [PowerSeries.coeff_mk, pow_succ, Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Matrix.mul_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [matrixGeomSeries, PowerSeries.coeff_mul_C]

theorem coe_charpolyRev (M : Matrix n n R) :
    ((M.charpolyRev : R[X]) : PowerSeries R) =
      (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C).det := by
  rw [Matrix.charpolyRev, ← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;>
    simp [h, Polynomial.coeToPowerSeries.ringHom_apply] <;> ring

theorem coe_derivative_charpolyRev (M : Matrix n n R) :
    ((derivative M.charpolyRev : R[X]) : PowerSeries R) =
      -(M.charpolyRev : PowerSeries R) * PowerSeries.mk fun k => (M ^ (k + 1)).trace := by
  set T : PowerSeries R := PowerSeries.X
  set N : Matrix n n (PowerSeries R) := M.map PowerSeries.C
  set A : Matrix n n (PowerSeries R) := 1 - T • N
  set B := matrixGeomSeries M
  have hAB : A * B = 1 := one_sub_X_smul_mul_matrixGeomSeries M

  set ψ : R[X] →+* (PowerSeries R)[X] :=
    (Polynomial.compRingHom (Polynomial.C T + Polynomial.X)).comp
      (Polynomial.mapRingHom PowerSeries.C)
  have hψ : ∀ p : R[X], ψ p = (p.map PowerSeries.C).comp (Polynomial.C T + Polynomial.X) :=
    fun p => rfl
  have hfac : ψ M.charpolyRev =
      Polynomial.C A.det * (1 + (Polynomial.X : (PowerSeries R)[X]) •
        (-(B * N)).map Polynomial.C).det := by
    rw [Matrix.charpolyRev, RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
    congr 1
    have h1 : A.map Polynomial.C * (1 + (Polynomial.X : (PowerSeries R)[X]) •
        (-(B * N)).map Polynomial.C) =
        A.map Polynomial.C - (Polynomial.X : (PowerSeries R)[X]) • N.map Polynomial.C := by
      rw [mul_add, mul_one, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_neg,
        ← Matrix.mul_assoc, hAB, Matrix.one_mul, Matrix.map_neg _ (map_neg Polynomial.C), smul_neg, sub_eq_add_neg]
    rw [show (Polynomial.C : PowerSeries R →+* (PowerSeries R)[X]).mapMatrix A =
      A.map Polynomial.C from rfl, h1]
    ext i j
    by_cases h : i = j <;>
      simp [hψ, A, N, T, h] <;> ring
  have hder : (derivative (ψ M.charpolyRev)).eval 0 =
      ((derivative M.charpolyRev : R[X]) : PowerSeries R) := by
    rw [hψ, Polynomial.derivative_comp, Polynomial.derivative_add, Polynomial.derivative_C,
      Polynomial.derivative_X, zero_add, one_mul, Polynomial.eval_comp, Polynomial.derivative_map,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, add_zero, Polynomial.eval_map,
      Polynomial.eval₂_C_X_eq_coe]
  rw [← hder, hfac, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Matrix.derivative_det_one_add_X_smul, Matrix.trace_neg, ← coe_charpolyRev,
    ← trace_matrixGeomSeries_mul, mul_neg, neg_mul]

end MatrixJacobi

section LogSeries

variable {k : Type*} [Field k] [CharZero k]

theorem mul_derivative_logOf (f : PowerSeries k) (hf : PowerSeries.constantCoeff f = 1) :
    f * PowerSeries.derivative k (PowerSeries.logOf f) = PowerSeries.derivative k f := by
  have h0 : PowerSeries.constantCoeff (f - 1) = 0 := by rw [map_sub, map_one, hf, sub_self]
  have ha : PowerSeries.HasSubst (f - 1) := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hgeom : (1 + PowerSeries.X) * PowerSeries.derivative k (PowerSeries.log k) = 1 := by
    rw [PowerSeries.deriv_log]
    ext n
    rcases n with _ | n
    · simp
    · simp [add_mul, PowerSeries.coeff_succ_X_mul, pow_succ]
  have h1 : (1 : PowerSeries k).subst (f - 1) = 1 := by
    rw [← PowerSeries.coe_substAlgHom ha, map_one]
  have hs : f * (PowerSeries.derivative k (PowerSeries.log k)).subst (f - 1) = 1 := by
    have := congrArg (PowerSeries.subst (f - 1)) hgeom
    rwa [PowerSeries.subst_mul ha, PowerSeries.subst_add ha, PowerSeries.subst_X ha, h1,
      add_sub_cancel] at this
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst ha, map_sub,
    Derivation.map_one_eq_zero, sub_zero, ← mul_assoc, hs, one_mul]

end LogSeries

section Endomorphism

variable {k W W' : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']

theorem reverse_charpoly_eq_charpolyRev {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k W) (A : Module.End k W) :
    A.charpoly.reverse = (LinearMap.toMatrix b b A).charpolyRev := by
  rw [← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]

theorem constantCoeff_reverse_charpoly (A : Module.End k W) :
    PowerSeries.constantCoeff (A.charpoly.reverse : PowerSeries k) = 1 := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_reverse,
    (LinearMap.charpoly_monic A).leadingCoeff]

theorem coe_derivative_reverse_charpoly (A : Module.End k W) :
    ((derivative A.charpoly.reverse : k[X]) : PowerSeries k) =
      -(A.charpoly.reverse : PowerSeries k) *
        PowerSeries.mk fun m => LinearMap.trace k W (A ^ (m + 1)) := by
  classical
  let b := Module.Free.chooseBasis k W
  rw [reverse_charpoly_eq_charpolyRev b, coe_derivative_charpolyRev]
  congr 2
  funext m
  rw [LinearMap.trace_eq_matrix_trace k b, LinearMap.toMatrix_pow]

theorem logOf_inv_reverse_charpoly [CharZero k] (A : Module.End k W) :
    PowerSeries.logOf ((A.charpoly.reverse : PowerSeries k)⁻¹) =
      PowerSeries.mk fun m => if m = 0 then 0 else LinearMap.trace k W (A ^ m) / m := by
  set P : PowerSeries k := ((A.charpoly.reverse : k[X]) : PowerSeries k) with hPdef
  set D : PowerSeries k := PowerSeries.mk fun m => LinearMap.trace k W (A ^ (m + 1))
  have hP : PowerSeries.constantCoeff P = 1 := constantCoeff_reverse_charpoly A
  have hPinv : PowerSeries.constantCoeff P⁻¹ = 1 := by
    rw [PowerSeries.constantCoeff_inv, hP, inv_one]
  have hPP : P * P⁻¹ = 1 := PowerSeries.mul_inv_cancel P (by rw [hP]; exact one_ne_zero)
  have hdP : PowerSeries.derivative k P = -P * D := by
    rw [hPdef, PowerSeries.derivative_coe, coe_derivative_reverse_charpoly]
  have key := mul_derivative_logOf P⁻¹ hPinv
  rw [PowerSeries.derivative_inv', hdP] at key
  apply PowerSeries.derivative.ext
  · have hD : PowerSeries.derivative k (PowerSeries.mk fun m =>
        if m = 0 then 0 else LinearMap.trace k W (A ^ m) / m) = D := by
      ext n
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, PowerSeries.coeff_mk, if_neg n.succ_ne_zero,
        Nat.cast_add_one, div_mul_cancel₀ _ (Nat.cast_add_one_ne_zero n)]
    rw [hD]
    calc PowerSeries.derivative k (PowerSeries.logOf P⁻¹)
        = P * (P⁻¹ * PowerSeries.derivative k (PowerSeries.logOf P⁻¹)) := by
          rw [← mul_assoc, hPP, one_mul]
      _ = P * (P⁻¹ * D * (P * P⁻¹)) := by rw [key]; ring
      _ = D := by rw [hPP, mul_one, ← mul_assoc, hPP, one_mul]
  · rw [PowerSeries.constantCoeff_logOf hPinv, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_mk, if_pos rfl]

theorem reverse_charpoly_eq_of_trace_pow_eq [CharZero k] (A : Module.End k W)
    (B : Module.End k W')
    (h : ∀ m, 0 < m → LinearMap.trace k W (A ^ m) = LinearMap.trace k W' (B ^ m)) :
    A.charpoly.reverse = B.charpoly.reverse := by
  set P : PowerSeries k := ((A.charpoly.reverse : k[X]) : PowerSeries k) with hPdef
  set Q : PowerSeries k := ((B.charpoly.reverse : k[X]) : PowerSeries k) with hQdef
  set D : PowerSeries k := PowerSeries.mk fun m => LinearMap.trace k W (A ^ (m + 1))
  have hP : PowerSeries.constantCoeff P = 1 := constantCoeff_reverse_charpoly A
  have hQ : PowerSeries.constantCoeff Q = 1 := constantCoeff_reverse_charpoly B
  have hQQ : Q⁻¹ * Q = 1 := PowerSeries.inv_mul_cancel Q (by rw [hQ]; exact one_ne_zero)
  have hdP : PowerSeries.derivative k P = -P * D := by
    rw [hPdef, PowerSeries.derivative_coe, coe_derivative_reverse_charpoly]
  have hdQ : PowerSeries.derivative k Q = -Q * D := by
    rw [hQdef, PowerSeries.derivative_coe, coe_derivative_reverse_charpoly]
    congr 2
    funext m
    exact (h (m + 1) m.succ_pos).symm
  have h1 : P * Q⁻¹ = 1 := by
    apply PowerSeries.derivative.ext
    · rw [Derivation.leibniz, PowerSeries.derivative_inv', hdP, hdQ,
        Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul]
      linear_combination (P * Q⁻¹ * D) * hQQ
    · rw [map_mul, PowerSeries.constantCoeff_inv, hP, hQ, map_one, inv_one, mul_one]
  have h2 : P = Q := by
    calc P = P * (Q⁻¹ * Q) := by rw [hQQ, mul_one]
      _ = Q := by rw [← mul_assoc, h1, one_mul]
  exact Polynomial.coe_inj.1 h2

end Endomorphism

end GroundTheory.Global
