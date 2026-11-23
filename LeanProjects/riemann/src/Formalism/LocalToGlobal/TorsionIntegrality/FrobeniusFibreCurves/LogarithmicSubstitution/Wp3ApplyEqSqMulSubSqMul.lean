import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementD

noncomputable section

namespace Formalism.L2.Th1.B.Det

open Formalism.InvariantFactorPaths.G7 (at1)

theorem tau_derivative_rule_holds : TauRule := by
  intro K _ _ g2 g3 P hP
  set U : MvPowerSeries (Fin 2) K := 1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P with hU
  have hU1 : MvPowerSeries.constantCoeff U = 1 := by simp [hU]
  have hW : wpDiff P = (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) * U :=
    Formalism.L2.Th1.B.Add0.wpDiff_eq dqRule hP.2.1
  have hL : par0 (sigS P) = fLog U := addSigmaLog K g2 g3 P hP
  have e0 := mul_pd_fLog (0 : Fin 2) hU1
  have e1 := mul_pd_fLog (1 : Fin 2) hU1
  have p0 := pderiv_zero_parallelogram_defect (sigS P)
  have p1 := pderiv_one_parallelogram_defect (sigS P)
  rw [hL] at p0 p1
  have x00 : pd 0 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 1 := MvPowerSeries.pderiv_X_self
  have x11 : pd 1 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 1 := MvPowerSeries.pderiv_X_self
  have x01 : pd 0 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp [MvPowerSeries.pderiv_X]
  have x10 : pd 1 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by
    simp [MvPowerSeries.pderiv_X]
  rw [hW]
  simp only [pd, Derivation.leibniz, map_sub, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at x00 x11 x01 x10 e0 e1 p0 p1 ⊢
  rw [x00, x11, x01, x10]
  linear_combination (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) * (-e0 + e1 + U * p0 - U * p1)

set_option maxHeartbeats 400000 in
theorem core {R : Type} [CommRing R] (a b c Xa Ya Xb Yb Xc Yc h g3 : R)
    (Ca : Ya ^ 2 = 4 * Xa ^ 3 - 2 * h * a ^ 4 * Xa - g3 * a ^ 6)
    (Cb : Yb ^ 2 = 4 * Xb ^ 3 - 2 * h * b ^ 4 * Xb - g3 * b ^ 6)
    (Cc : Yc ^ 2 = 4 * Xc ^ 3 - 2 * h * c ^ 4 * Xc - g3 * c ^ 6) :
    2 * (a ^ 2 * Xb - b ^ 2 * Xa) * (a ^ 2 * Xc - c ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) * a *
      (c * (a ^ 3 * (b * (3 * Xb + Yb) * Yc - (6 * Xb ^ 2 - h * b ^ 4 + 3 * Yb) * (c * Xc)) -
          a * Xa * (3 * b ^ 3 * Yc - (6 * Xb ^ 2 - h * b ^ 4 + 3 * Yb) * c ^ 3) +
          Ya * (3 * b ^ 3 * (c * Xc) - b * (3 * Xb + Yb) * c ^ 3)) -
        b * (a ^ 3 * (b * Xb * (6 * Xc ^ 2 - h * c ^ 4 + 3 * Yc) - Yb * (c * (3 * Xc + Yc))) -
          a * Xa * (b ^ 3 * (6 * Xc ^ 2 - h * c ^ 4 + 3 * Yc) - Yb * (3 * c ^ 3)) +
          Ya * (b ^ 3 * (c * (3 * Xc + Yc)) - b * Xb * (3 * c ^ 3)))) =
    (a ^ 3 * (b * Xb * Yc - Yb * (c * Xc)) - a * Xa * (b ^ 3 * Yc - Yb * c ^ 3) +
        Ya * (b ^ 3 * (c * Xc) - b * Xb * c ^ 3)) *
      (-c * (b * (2 * a ^ 2 * Xb - b ^ 2 * (Ya + 2 * Xa)) -
            a * (a ^ 2 * (Yb + 2 * Xb) - 2 * b ^ 2 * Xa)) *
          (a ^ 2 * Xc - c ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) +
        b * (c * (2 * a ^ 2 * Xc - c ^ 2 * (Ya + 2 * Xa)) -
            a * (a ^ 2 * (Yc + 2 * Xc) - 2 * c ^ 2 * Xa)) *
          (a ^ 2 * Xb - b ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) +
        2 * a * (c * (2 * b ^ 2 * Xc - c ^ 2 * (Yb + 2 * Xb)) -
            b * (b ^ 2 * (Yc + 2 * Xc) - 2 * c ^ 2 * Xb)) *
          (a ^ 2 * Xb - b ^ 2 * Xa) * (a ^ 2 * Xc - c ^ 2 * Xa)) := by
  linear_combination (-a^2*b^2*c^2*(-Xb*c^2 + Xc*b^2)^3) * Ca + (a^2*c^2*(-Xa*c^2 + Xc*a^2)^2*(2*Xa*b^2*c^2 - 3*Xb*a^2*c^2 + Xc*a^2*b^2)) * Cb +
    (a^2*b^2*(-Xa*b^2 + Xb*a^2)^2*(-2*Xa*b^2*c^2 - Xb*a^2*c^2 + 3*Xc*a^2*b^2)) * Cc

section

variable {K : Type} [Field K] [CharZero K]

local notation "A3" => MvPowerSeries (Fin 3) K

theorem triple_lintegral_eq (x : Fin 3) (f : PowerSeries K) :
    (at1 x f : A3) = PowerSeries.substAlgHom (PowerSeries.HasSubst.X x) f := by
  rw [PowerSeries.coe_substAlgHom]; rfl

theorem series_at_variable_const (x : Fin 3) (c : K) : (at1 x (PowerSeries.C c) : A3) = MvPowerSeries.C c := by
  show PowerSeries.subst (MvPowerSeries.X x : A3) (PowerSeries.C c) = MvPowerSeries.C c
  exact PowerSeries.subst_C c

theorem pderiv_series_at_variable (i x : Fin 3) (f : PowerSeries K) :
    pd i (at1 x f : A3) = at1 x (dz f) * pd i (MvPowerSeries.X x : A3) := by
  show MvPowerSeries.pderiv K i (PowerSeries.subst (MvPowerSeries.X x : A3) f) =
    PowerSeries.subst (MvPowerSeries.X x : A3) (PowerSeries.derivative K f) * MvPowerSeries.pderiv K i (MvPowerSeries.X x : A3)
  exact Formalism.G.LogCR.pderiv_psubst (by simp) f i

theorem partialDeriv_inVar_self (x : Fin 3) (f : PowerSeries K) : pd x (at1 x f : A3) = at1 x (dz f) := by
  rw [pderiv_series_at_variable, show pd x (MvPowerSeries.X x : A3) = 1 from MvPowerSeries.pderiv_X_self, mul_one]

theorem partialDeriv_inVar_of_ne {i x : Fin 3} (h : x ≠ i) (f : PowerSeries K) : pd i (at1 x f : A3) = 0 := by
  rw [pderiv_series_at_variable, show pd i (MvPowerSeries.X x : A3) = 0 by
    simp [MvPowerSeries.pderiv_X, Pi.single_eq_of_ne h], mul_zero]

theorem X_ne (j : Fin 3) : (MvPowerSeries.X j : A3) ≠ 0 := by
  intro h
  have h' := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) h
  simp [MvPowerSeries.coeff_X] at h'

def Xt (P : PowerSeries K) (j : Fin 3) : A3 := 1 + MvPowerSeries.X j ^ 2 * at1 j P

def Yt (P : PowerSeries K) (j : Fin 3) : A3 := -2 + MvPowerSeries.X j ^ 3 * at1 j (dz P)

def dXt (P : PowerSeries K) (j : Fin 3) : A3 :=
  2 * MvPowerSeries.X j * at1 j P + MvPowerSeries.X j ^ 2 * at1 j (dz P)

def dYt (P : PowerSeries K) (j : Fin 3) : A3 :=
  3 * MvPowerSeries.X j ^ 2 * at1 j (dz P) + MvPowerSeries.X j ^ 3 * at1 j (dz (dz P))

theorem pd_Xt_self (P : PowerSeries K) (j : Fin 3) :
    MvPowerSeries.pderiv K j (Xt P j) = dXt P j := by
  simp only [Xt, dXt, map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_one_eq_zero,
    MvPowerSeries.pderiv_X_self, partialDeriv_inVar_self, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem pd_Xt_ne (P : PowerSeries K) {i j : Fin 3} (h : j ≠ i) :
    MvPowerSeries.pderiv K i (Xt P j) = 0 := by
  simp [Xt, Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X, Pi.single_eq_of_ne h,
    partialDeriv_inVar_of_ne h]

theorem pd_neg_two (i : Fin 3) : MvPowerSeries.pderiv K i (-2 : A3) = 0 := by
  have h2 : MvPowerSeries.pderiv K i (2 : A3) = 0 := by
    simpa using (MvPowerSeries.pderiv K i).map_natCast 2
  rw [map_neg, h2, neg_zero]

theorem pd_Yt_self (P : PowerSeries K) (j : Fin 3) :
    MvPowerSeries.pderiv K j (Yt P j) = dYt P j := by
  simp only [Yt, dYt, map_add, Derivation.leibniz, Derivation.leibniz_pow, pd_neg_two,
    MvPowerSeries.pderiv_X_self, partialDeriv_inVar_self, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem pd_Yt_ne (P : PowerSeries K) {i j : Fin 3} (h : j ≠ i) :
    MvPowerSeries.pderiv K i (Yt P j) = 0 := by
  simp [Yt, Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X, Pi.single_eq_of_ne h,
    partialDeriv_inVar_of_ne h, pd_neg_two]

theorem wp3_apply_eq_sq_mul_sub_sq_mul (P : PowerSeries K) (j k : Fin 3) :
    wp3 P j k = MvPowerSeries.X j ^ 2 * Xt P k - MvPowerSeries.X k ^ 2 * Xt P j := by
  simp only [wp3, Xt]
  ring

theorem det_three_points_eq_expansion (P : PowerSeries K) :
    det3 P = MvPowerSeries.X 0 ^ 3 * (MvPowerSeries.X 1 * Xt P 1 * Yt P 2 -
        Yt P 1 * (MvPowerSeries.X 2 * Xt P 2)) -
      MvPowerSeries.X 0 * Xt P 0 * (MvPowerSeries.X 1 ^ 3 * Yt P 2 -
        Yt P 1 * MvPowerSeries.X 2 ^ 3) +
      Yt P 0 * (MvPowerSeries.X 1 ^ 3 * (MvPowerSeries.X 2 * Xt P 2) -
        MvPowerSeries.X 1 * Xt P 1 * MvPowerSeries.X 2 ^ 3) := by
  simp [det3, Matrix.det_fin_three, Xt, Yt]
  ring

theorem X_mul_dXt (P : PowerSeries K) (j : Fin 3) :
    MvPowerSeries.X j * dXt P j = Yt P j + 2 * Xt P j := by
  simp only [dXt, Yt, Xt]
  ring

theorem curve_eq {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) (j : Fin 3) :
    Yt P j ^ 2 = 4 * Xt P j ^ 3 - 2 * MvPowerSeries.C (g2 / 2) * MvPowerSeries.X j ^ 4 * Xt P j -
      MvPowerSeries.C g3 * MvPowerSeries.X j ^ 6 := by
  have h' := congrArg (PowerSeries.substAlgHom (R := K) (PowerSeries.HasSubst.X (S := K) (τ := Fin 3) j)) hP.2.2
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X (R := K) (PowerSeries.HasSubst.X (S := K) j), PowerSeries.subst_C] at h'
  have hc : (MvPowerSeries.C g2 : A3) = 2 * MvPowerSeries.C (g2 / 2) := by
    conv_lhs => rw [show g2 = 2 * (g2 / 2) by ring]
    rw [map_mul, map_ofNat]
  simp only [Xt, Yt, Formalism.InvariantFactorPaths.G7.at1]
  linear_combination h' - (MvPowerSeries.X j ^ 4 * (1 + MvPowerSeries.X j ^ 2 * PowerSeries.subst (MvPowerSeries.X j : A3) P)) * hc

theorem X_mul_dYt {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) (j : Fin 3) :
    MvPowerSeries.X j * dYt P j =
      6 * Xt P j ^ 2 - MvPowerSeries.C (g2 / 2) * MvPowerSeries.X j ^ 4 + 3 * Yt P j := by
  have h' := congrArg (PowerSeries.substAlgHom (R := K) (PowerSeries.HasSubst.X (S := K) (τ := Fin 3) j)) (wpReduced K g2 g3 P hP).2
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X (R := K) (PowerSeries.HasSubst.X (S := K) j), PowerSeries.subst_C] at h'
  simp only [dYt, Xt, Yt, Formalism.InvariantFactorPaths.G7.at1]
  linear_combination MvPowerSeries.X j ^ 2 * h'

theorem pderiv_left_weierstrass_pair (P : PowerSeries K) {j k : Fin 3} (h : k ≠ j) :
    pd j (wp3 P j k) = 2 * MvPowerSeries.X j * Xt P k - MvPowerSeries.X k ^ 2 * dXt P j := by
  rw [wp3_apply_eq_sq_mul_sub_sq_mul]
  simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X_self,
    MvPowerSeries.pderiv_X, Pi.single_eq_of_ne h, pd_Xt_self, pd_Xt_ne P h, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem pderiv_right_weierstrass_pair (P : PowerSeries K) {j k : Fin 3} (h : j ≠ k) :
    pd k (wp3 P j k) = MvPowerSeries.X j ^ 2 * dXt P k - 2 * MvPowerSeries.X k * Xt P j := by
  rw [wp3_apply_eq_sq_mul_sub_sq_mul]
  simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X_self,
    MvPowerSeries.pderiv_X, Pi.single_eq_of_ne h, pd_Xt_self, pd_Xt_ne P h, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem pderiv_one_det_three_points (P : PowerSeries K) :
    pd 1 (det3 P) = MvPowerSeries.X 0 ^ 3 * ((Xt P 1 + MvPowerSeries.X 1 * dXt P 1) * Yt P 2 -
        dYt P 1 * (MvPowerSeries.X 2 * Xt P 2)) -
      MvPowerSeries.X 0 * Xt P 0 * (3 * MvPowerSeries.X 1 ^ 2 * Yt P 2 -
        dYt P 1 * MvPowerSeries.X 2 ^ 3) +
      Yt P 0 * (3 * MvPowerSeries.X 1 ^ 2 * (MvPowerSeries.X 2 * Xt P 2) -
        (Xt P 1 + MvPowerSeries.X 1 * dXt P 1) * MvPowerSeries.X 2 ^ 3) := by
  have h0 : (0 : Fin 3) ≠ 1 := by decide
  have h2 : (2 : Fin 3) ≠ 1 := by decide
  rw [det_three_points_eq_expansion]
  simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X_self,
    MvPowerSeries.pderiv_X, Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h2, pd_Xt_self, pd_Xt_ne P h0,
    pd_Xt_ne P h2, pd_Yt_self, pd_Yt_ne P h0, pd_Yt_ne P h2, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem pderiv_two_det_three_points (P : PowerSeries K) :
    pd 2 (det3 P) = MvPowerSeries.X 0 ^ 3 * (MvPowerSeries.X 1 * Xt P 1 * dYt P 2 -
        Yt P 1 * (Xt P 2 + MvPowerSeries.X 2 * dXt P 2)) -
      MvPowerSeries.X 0 * Xt P 0 * (MvPowerSeries.X 1 ^ 3 * dYt P 2 -
        Yt P 1 * (3 * MvPowerSeries.X 2 ^ 2)) +
      Yt P 0 * (MvPowerSeries.X 1 ^ 3 * (Xt P 2 + MvPowerSeries.X 2 * dXt P 2) -
        MvPowerSeries.X 1 * Xt P 1 * (3 * MvPowerSeries.X 2 ^ 2)) := by
  have h0 : (0 : Fin 3) ≠ 2 := by decide
  have h1 : (1 : Fin 3) ≠ 2 := by decide
  rw [det_three_points_eq_expansion]
  simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X_self,
    MvPowerSeries.pderiv_X, Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1, pd_Xt_self, pd_Xt_ne P h0,
    pd_Xt_ne P h1, pd_Yt_self, pd_Yt_ne P h0, pd_Yt_ne P h1, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

end

theorem core2 {R : Type} [CommRing R] (a b c Xa Ya Xb Yb Xc Yc h g3 dXa dXb dXc dYb dYc : R)
    (Ca : Ya ^ 2 = 4 * Xa ^ 3 - 2 * h * a ^ 4 * Xa - g3 * a ^ 6)
    (Cb : Yb ^ 2 = 4 * Xb ^ 3 - 2 * h * b ^ 4 * Xb - g3 * b ^ 6)
    (Cc : Yc ^ 2 = 4 * Xc ^ 3 - 2 * h * c ^ 4 * Xc - g3 * c ^ 6)
    (ha : a * dXa = Ya + 2 * Xa) (hb : b * dXb = Yb + 2 * Xb) (hc : c * dXc = Yc + 2 * Xc)
    (kb : b * dYb = 6 * Xb ^ 2 - h * b ^ 4 + 3 * Yb)
    (kc : c * dYc = 6 * Xc ^ 2 - h * c ^ 4 + 3 * Yc) :
    (a * b * c) * (2 * (a ^ 2 * Xb - b ^ 2 * Xa) * (a ^ 2 * Xc - c ^ 2 * Xa) *
        (b ^ 2 * Xc - c ^ 2 * Xb) *
      ((a ^ 3 * ((Xb + b * dXb) * Yc - dYb * (c * Xc)) -
          a * Xa * (3 * b ^ 2 * Yc - dYb * c ^ 3) +
          Ya * (3 * b ^ 2 * (c * Xc) - (Xb + b * dXb) * c ^ 3)) -
        (a ^ 3 * (b * Xb * dYc - Yb * (Xc + c * dXc)) -
          a * Xa * (b ^ 3 * dYc - Yb * (3 * c ^ 2)) +
          Ya * (b ^ 3 * (Xc + c * dXc) - b * Xb * (3 * c ^ 2))))) =
    (a * b * c) * ((a ^ 3 * (b * Xb * Yc - Yb * (c * Xc)) - a * Xa * (b ^ 3 * Yc - Yb * c ^ 3) +
        Ya * (b ^ 3 * (c * Xc) - b * Xb * c ^ 3)) *
      (-((2 * a * Xb - b ^ 2 * dXa) - (a ^ 2 * dXb - 2 * b * Xa)) *
          (a ^ 2 * Xc - c ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) +
        ((2 * a * Xc - c ^ 2 * dXa) - (a ^ 2 * dXc - 2 * c * Xa)) *
          (a ^ 2 * Xb - b ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) +
        2 * ((2 * b * Xc - c ^ 2 * dXb) - (b ^ 2 * dXc - 2 * c * Xb)) *
          (a ^ 2 * Xb - b ^ 2 * Xa) * (a ^ 2 * Xc - c ^ 2 * Xa))) := by
  linear_combination (-a^2*b*c*(-Xb*c^2 + Xc*b^2)^2*(Xa*Yb*a*c^3 - Xa*Yc*a*b^3 - Xb*Ya*b*c^3 + Xb*Yc*a^3*b + Xc*Ya*b^3*c - Xc*Yb*a^3*c)) * ha +
    (a^2*c*(-Xa*c^2 + Xc*a^2)*(-2*Xa^2*Yb*b^2*c^5 + 2*Xa^2*Yc*b^5*c^2 + 3*Xa*Xb*Yb*a^2*c^5 - 3*Xa*Xb*Yc*a^2*b^3*c^2 + Xa*Xc*Yb*a^2*b^2*c^3 - Xa*Xc*Yc*a^2*b^5 - Xb^2*Ya*a*b*c^5 + Xb^2*Yc*a^4*b*c^2 + 2*Xb*Xc*Ya*a*b^3*c^3 - 3*Xb*Xc*Yb*a^4*c^3 + Xb*Xc*Yc*a^4*b^3 - Xc^2*Ya*a*b^5*c + Xc^2*Yb*a^4*b^2*c)) * hb +
    (a^2*b*(-Xa*b^2 + Xb*a^2)*(-2*Xa^2*Yb*b^2*c^5 + 2*Xa^2*Yc*b^5*c^2 + Xa*Xb*Yb*a^2*c^5 - Xa*Xb*Yc*a^2*b^3*c^2 + 3*Xa*Xc*Yb*a^2*b^2*c^3 - 3*Xa*Xc*Yc*a^2*b^5 + Xb^2*Ya*a*b*c^5 - Xb^2*Yc*a^4*b*c^2 - 2*Xb*Xc*Ya*a*b^3*c^3 - Xb*Xc*Yb*a^4*c^3 + 3*Xb*Xc*Yc*a^4*b^3 + Xc^2*Ya*a*b^5*c - Xc^2*Yb*a^4*b^2*c)) * hc +
    (-2*a^2*c^2*(-Xa*b^2 + Xb*a^2)*(-Xa*c^2 + Xc*a^2)^2*(-Xb*c^2 + Xc*b^2)) * kb + (-2*a^2*b^2*(-Xa*b^2 + Xb*a^2)^2*(-Xa*c^2 + Xc*a^2)*(-Xb*c^2 + Xc*b^2)) * kc +
    core a b c Xa Ya Xb Yb Xc Yc h g3 Ca Cb Cc

theorem determinant_derivative_rule_holds : DetRule := by
  intro K _ _ g2 g3 P hP
  have key := core2 (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) (MvPowerSeries.X 1) (MvPowerSeries.X 2) (Xt P 0) (Yt P 0)
    (Xt P 1) (Yt P 1) (Xt P 2) (Yt P 2) (MvPowerSeries.C (g2 / 2)) (MvPowerSeries.C g3)
    (dXt P 0) (dXt P 1) (dXt P 2) (dYt P 1) (dYt P 2) (curve_eq hP 0) (curve_eq hP 1)
    (curve_eq hP 2) (X_mul_dXt P 0) (X_mul_dXt P 1) (X_mul_dXt P 2) (X_mul_dYt hP 1)
    (X_mul_dYt hP 2)
  have habc : (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (X_ne 0) (X_ne 1)) (X_ne 2)
  rw [pderiv_one_det_three_points, pderiv_two_det_three_points, pderiv_left_weierstrass_pair P (by decide : (1 : Fin 3) ≠ 0),
    pderiv_right_weierstrass_pair P (by decide : (0 : Fin 3) ≠ 1), pderiv_left_weierstrass_pair P (by decide : (2 : Fin 3) ≠ 0),
    pderiv_right_weierstrass_pair P (by decide : (0 : Fin 3) ≠ 2), pderiv_left_weierstrass_pair P (by decide : (2 : Fin 3) ≠ 1),
    pderiv_right_weierstrass_pair P (by decide : (1 : Fin 3) ≠ 2), wp3_apply_eq_sq_mul_sub_sq_mul, wp3_apply_eq_sq_mul_sub_sq_mul, wp3_apply_eq_sq_mul_sub_sq_mul, det_three_points_eq_expansion]
  apply mul_left_cancel₀ habc
  linear_combination key

end Formalism.L2.Th1.B.Det
