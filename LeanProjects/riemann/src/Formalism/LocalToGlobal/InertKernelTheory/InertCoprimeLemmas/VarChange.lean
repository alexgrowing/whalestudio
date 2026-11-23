import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll

open PowerSeries

noncomputable section

namespace Formalism.L2.KerInert.VC

section Alg

variable {A : Type*} [CommRing A] (a1 a2 a3 a4 a6 U Ui r s t u w v : A)

theorem weq_vc (hw : w = u^3 + a1*u*w + a2*u^2*w + a3*w^2 + a4*u*w^2 + a6*w^3)
    (hv : v * (1 + s*u + (t - s*r)*w) = 1) (hU : U * Ui = 1) :
    (U^3*w*v) = (U*(u - r*w)*v)^3 + (Ui*(a1+2*s))*(U*(u - r*w)*v)*(U^3*w*v) + (Ui^2*(a2 - s*a1 + 3*r - s^2))*(U*(u - r*w)*v)^2*(U^3*w*v) + (Ui^3*(a3 + r*a1 + 2*t))*(U^3*w*v)^2 + (Ui^4*(a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r^2 - 2*s*t))*(U*(u - r*w)*v)*(U^3*w*v)^2 + (Ui^6*(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1))*(U^3*w*v)^3 := by
  linear_combination (U^3*v^3*(1)) * hw + (U^3*(v^3*((-a1*r*s*u*w^2 + a1*s*u^2*w + a1*t*u*w^2 - a2*u^2*w - a3*r*s*w^3 + a3*s*u*w^2 + a3*t*w^3 - a4*u*w^2 - a6*w^3 + r^2*s^2*w^3 - 2*r*s^2*u*w^2 - 2*r*s*t*w^3 + s^2*u^2*w + 2*s*t*u*w^2 + t^2*w^3 - u^3)*(1 + s*u + (t - s*r)*w)^0*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1 + (v*(1 + s*u + (t - s*r)*w))^2) + (-a1*u*w - a3*w^2 + 2*r*s*w^2 - 2*s*u*w - 2*t*w^2)*(1 + s*u + (t - s*r)*w)^1*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1) + (w)*(1 + s*u + (t - s*r)*w)^2*((v*(1 + s*u + (t - s*r)*w))^0)) - (-a1*r*s*u*v^3*w^2 + a1*s*u^2*v^3*w + a1*t*u*v^3*w^2 - a1*u*v^2*w - a2*u^2*v^3*w - a3*r*s*v^3*w^3 + a3*s*u*v^3*w^2 + a3*t*v^3*w^3 - a3*v^2*w^2 - a4*u*v^3*w^2 - a6*v^3*w^3 + r^2*s^2*v^3*w^3 - 2*r*s^2*u*v^3*w^2 - 2*r*s*t*v^3*w^3 + 2*r*s*v^2*w^2 + s^2*u^2*v^3*w + 2*s*t*u*v^3*w^2 - 2*s*u*v^2*w + t^2*v^3*w^3 - 2*t*v^2*w^2 - u^3*v^3 + v*w)*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1 + (v*(1 + s*u + (t - s*r)*w))^2))) * hv + (U^3*(a1*r*t*v^3*w^3 - a2*r^2*v^3*w^3 + a3*t*v^3*w^3 - a4*r*v^3*w^3 - a6*v^3*w^3 - r^3*v^3*w^3 + t^2*v^3*w^3)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3 + (U*Ui)^4 + (U*Ui)^5) + U^3*(-a1*r^2*s*v^3*w^3 + a1*r*s*u*v^3*w^2 - a1*r*t*v^3*w^3 + a1*t*u*v^3*w^2 + 2*a2*r^2*v^3*w^3 - 2*a2*r*u*v^3*w^2 - a3*r*s*v^3*w^3 + a3*s*u*v^3*w^2 + a4*r*v^3*w^3 - a4*u*v^3*w^2 + 3*r^3*v^3*w^3 - 3*r^2*u*v^3*w^2 - 2*r*s*t*v^3*w^3 + 2*s*t*u*v^3*w^2)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3) + U^3*(-a1*r*v^2*w^2 - a3*v^2*w^2 - 2*t*v^2*w^2)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2) + U^3*(a1*r^2*s*v^3*w^3 - 2*a1*r*s*u*v^3*w^2 + a1*s*u^2*v^3*w - a2*r^2*v^3*w^3 + 2*a2*r*u*v^3*w^2 - a2*u^2*v^3*w - 3*r^3*v^3*w^3 + r^2*s^2*v^3*w^3 + 6*r^2*u*v^3*w^2 - 2*r*s^2*u*v^3*w^2 - 3*r*u^2*v^3*w + s^2*u^2*v^3*w)*((U*Ui)^0 + (U*Ui)^1) + U^3*(a1*r*v^2*w^2 - a1*u*v^2*w + 2*r*s*v^2*w^2 - 2*s*u*v^2*w)*((U*Ui)^0)) * hU

theorem flow_vc (hw : w = u^3 + a1*u*w + a2*u^2*w + a3*w^2 + a4*u*w^2 + a6*w^3)
    (hv : v * (1 + s*u + (t - s*r)*w) = 1) (hU : U * Ui = 1) :
    U*(((1 - a1*u - a2*u^2 - 2*a3*w - 2*a4*u*w - 3*a6*w^2) - r*(3*u^2 + a1*w + 2*a2*u*w + a4*w^2))*v + (u - r*w)*(-v^2*(s*(1 - a1*u - a2*u^2 - 2*a3*w - 2*a4*u*w - 3*a6*w^2) + (t - s*r)*(3*u^2 + a1*w + 2*a2*u*w + a4*w^2)))) =
      U*(1 - (Ui*(a1+2*s))*(U*(u - r*w)*v) - (Ui^2*(a2 - s*a1 + 3*r - s^2))*(U*(u - r*w)*v)^2 - 2*(Ui^3*(a3 + r*a1 + 2*t))*(U^3*w*v) - 2*(Ui^4*(a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r^2 - 2*s*t))*(U*(u - r*w)*v)*(U^3*w*v) - 3*(Ui^6*(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1))*(U^3*w*v)^2) := by
  linear_combination (U^1*v^2*(3*t)) * hw + (U^1*(v^2*((-3*a1*t*u*w - 2*a2*r^2*s*u*w^2 + a2*r*s*u^2*w + 2*a2*r*t*u*w^2 + 2*a2*r*u*w + a2*s*u^3 - 2*a2*t*u^2*w + a2*u^2 - 3*a3*t*w^2 - a4*r^2*s*w^3 - a4*r*s*u*w^2 + a4*r*t*w^3 + a4*r*w^2 + 2*a4*s*u^2*w - a4*t*u*w^2 + 2*a4*u*w - 3*a6*r*s*w^3 + 3*a6*s*u*w^2 + 3*a6*w^2 - r^2*s^2*w^2 - 3*r^2*s*u^2*w + 2*r*s^2*u*w + 4*r*s*t*w^2 + 3*r*s*u^3 + r*s*w + 3*r*t*u^2*w + 3*r*u^2 - s^2*u^2 - 4*s*t*u*w - s*u - 3*t^2*w^2 - 3*t*u^3)*(1 + s*u + (t - s*r)*w)^0*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1) + (-2*a2*r*u*w - a2*u^2 - a4*r*w^2 - 2*a4*u*w - 3*a6*w^2 - 2*r*s*w - 3*r*u^2 + 2*s*u + 4*t*w + 1)*(1 + s*u + (t - s*r)*w)^1*((v*(1 + s*u + (t - s*r)*w))^0)) - (-3*a1*t*u*v^2*w - 2*a2*r^2*s*u*v^2*w^2 + a2*r*s*u^2*v^2*w + 2*a2*r*t*u*v^2*w^2 + 2*a2*r*u*v^2*w - 2*a2*r*u*v*w + a2*s*u^3*v^2 - 2*a2*t*u^2*v^2*w + a2*u^2*v^2 - a2*u^2*v - 3*a3*t*v^2*w^2 - a4*r^2*s*v^2*w^3 - a4*r*s*u*v^2*w^2 + a4*r*t*v^2*w^3 + a4*r*v^2*w^2 - a4*r*v*w^2 + 2*a4*s*u^2*v^2*w - a4*t*u*v^2*w^2 + 2*a4*u*v^2*w - 2*a4*u*v*w - 3*a6*r*s*v^2*w^3 + 3*a6*s*u*v^2*w^2 + 3*a6*v^2*w^2 - 3*a6*v*w^2 - r^2*s^2*v^2*w^2 - 3*r^2*s*u^2*v^2*w + 2*r*s^2*u*v^2*w + 4*r*s*t*v^2*w^2 + 3*r*s*u^3*v^2 + r*s*v^2*w - 2*r*s*v*w + 3*r*t*u^2*v^2*w + 3*r*u^2*v^2 - 3*r*u^2*v - s^2*u^2*v^2 - 4*s*t*u*v^2*w - s*u*v^2 + 2*s*u*v - 3*t^2*v^2*w^2 - 3*t*u^3*v^2 + 4*t*v*w + v - 1)*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1))) * hv + (U^1*(-3*a1*r*t*v^2*w^2 + 3*a2*r^2*v^2*w^2 - 3*a3*t*v^2*w^2 + 3*a4*r*v^2*w^2 + 3*a6*v^2*w^2 + 3*r^3*v^2*w^2 - 3*t^2*v^2*w^2)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3 + (U*Ui)^4 + (U*Ui)^5) + U^1*(2*a1*r^2*s*v^2*w^2 - 2*a1*r*s*u*v^2*w + 2*a1*r*t*v^2*w^2 - 2*a1*t*u*v^2*w - 4*a2*r^2*v^2*w^2 + 4*a2*r*u*v^2*w + 2*a3*r*s*v^2*w^2 - 2*a3*s*u*v^2*w - 2*a4*r*v^2*w^2 + 2*a4*u*v^2*w - 6*r^3*v^2*w^2 + 6*r^2*u*v^2*w + 4*r*s*t*v^2*w^2 - 4*s*t*u*v^2*w)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3) + U^1*(2*a1*r*v*w + 2*a3*v*w + 4*t*v*w)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2) + U^1*(-a1*r^2*s*v^2*w^2 + 2*a1*r*s*u*v^2*w - a1*s*u^2*v^2 + a2*r^2*v^2*w^2 - 2*a2*r*u*v^2*w + a2*u^2*v^2 + 3*r^3*v^2*w^2 - r^2*s^2*v^2*w^2 - 6*r^2*u*v^2*w + 2*r*s^2*u*v^2*w + 3*r*u^2*v^2 - s^2*u^2*v^2)*((U*Ui)^0 + (U*Ui)^1) + U^1*(-a1*r*v*w + a1*u*v - 2*r*s*v*w + 2*s*u*v)*((U*Ui)^0)) * hU

end Alg

open Formalism.L2.Th1.A

section Ring

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)

def den : R⟦X⟧ := 1 + PowerSeries.C C.s * X + PowerSeries.C (C.t - C.s * C.r) * wSer W

def vv : R⟦X⟧ := invOfUnit (den W C) 1

def phi : R⟦X⟧ := PowerSeries.C (C.u : R) * (X - PowerSeries.C C.r * wSer W) * vv W C

def psi : R⟦X⟧ := PowerSeries.C ((C.u : R) ^ 3) * wSer W * vv W C

theorem den_cc : constantCoeff (den W C) = 1 := by
  simp [den, CurveSer.wSer_cc]

theorem den_mul_vv : den W C * vv W C = 1 :=
  mul_invOfUnit _ _ (by rw [den_cc]; simp)

theorem vv_cc : constantCoeff (vv W C) = 1 := by
  simp [vv]

theorem phi_cc : constantCoeff (phi W C) = 0 := by
  simp [phi, CurveSer.wSer_cc]

theorem psi_cc : constantCoeff (psi W C) = 0 := by
  simp [psi, CurveSer.wSer_cc]

theorem phi_eq : phi W C = X * (PowerSeries.C (C.u : R) * (1 - PowerSeries.C C.r * X ^ 2 * wU W) * vv W C) := by
  rw [phi, CurveSer.wSer_eq]; ring

theorem phi_coeff_one : coeff 1 (phi W C) = (C.u : R) := by
  rw [phi_eq, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  simp [vv_cc]

theorem hU_C : PowerSeries.C (C.u : R) * PowerSeries.C ((C.u⁻¹ : Rˣ) : R) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

theorem hv_C : vv W C * (1 + PowerSeries.C C.s * X + (PowerSeries.C C.t - PowerSeries.C C.s * PowerSeries.C C.r) * wSer W) = 1 := by
  rw [mul_comm, ← map_mul, ← map_sub]; exact den_mul_vv W C

theorem weq_phi : psi W C = phi W C ^ 3 + PowerSeries.C (C • W).a₁ * phi W C * psi W C
    + PowerSeries.C (C • W).a₂ * phi W C ^ 2 * psi W C + PowerSeries.C (C • W).a₃ * psi W C ^ 2
    + PowerSeries.C (C • W).a₄ * phi W C * psi W C ^ 2 + PowerSeries.C (C • W).a₆ * psi W C ^ 3 := by
  have hw := (CurveSer.wSer_fixed W).2
  have h := weq_vc (PowerSeries.C W.a₁) (PowerSeries.C W.a₂) (PowerSeries.C W.a₃) (PowerSeries.C W.a₄)
    (PowerSeries.C W.a₆) (PowerSeries.C (C.u : R)) (PowerSeries.C ((C.u⁻¹ : Rˣ) : R)) (PowerSeries.C C.r)
    (PowerSeries.C C.s) (PowerSeries.C C.t) X (wSer W) (vv W C) hw (hv_C W C) (hU_C C)
  simp only [phi, psi, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆,
    map_mul, map_add, map_sub, map_pow, map_ofNat]
  linear_combination h

theorem wSer_phi : (wSer (C • W)).subst (phi W C) = psi W C :=
  (ISer.eq_wSer_subst wSerSpec (C • W) _ _ (phi_cc W C) (psi_cc W C) (weq_phi W C)).symm

theorem C_eq_algebraMap (a : R) : (PowerSeries.C a : R⟦X⟧) = algebraMap R R⟦X⟧ a := rfl

theorem D_C (a : R) : D W (PowerSeries.C a) = 0 := by
  rw [C_eq_algebraMap, Derivation.map_algebraMap]

theorem D_phi : D W (phi W C) = PowerSeries.C (C.u : R) * (fw (C • W)).subst (phi W C) := by
  obtain ⟨-, -, hFl, hfwAt, hfuAt, -⟩ := flowU R W
  obtain ⟨-, hDX, hDw⟩ := hFl
  rw [hfwAt] at hDX
  rw [hfuAt] at hDw
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have hfwsub : (fw (C • W)).subst (phi W C) = 1 - PowerSeries.C (C • W).a₁ * phi W C
      - PowerSeries.C (C • W).a₂ * phi W C ^ 2 - 2 * PowerSeries.C (C • W).a₃ * psi W C
      - 2 * PowerSeries.C (C • W).a₄ * phi W C * psi W C - 3 * PowerSeries.C (C • W).a₆ * psi W C ^ 2 := by
    rw [← ISer.subHom_apply _ (phi_cc W C)]
    simp only [fw, map_sub, map_mul, map_pow, map_one, map_ofNat, ISer.subHom_X, ISer.subHom_C]
    rw [ISer.subHom_apply, wSer_phi]
  have hvD : D W (vv W C) = -(vv W C) ^ 2 * D W (den W C) := by
    have h1 : D W (den W C * vv W C) = 0 := by rw [den_mul_vv, Derivation.map_one_eq_zero]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
    have h2 := den_mul_vv W C
    linear_combination (vv W C) * h1 - (D W (vv W C)) * h2
  have hdenD : D W (den W C) = PowerSeries.C C.s * D W X + PowerSeries.C (C.t - C.s * C.r) * D W (wSer W) := by
    simp only [den, map_add, Derivation.leibniz, smul_eq_mul, D_C, Derivation.map_one_eq_zero]
    ring
  have hphiD : D W (phi W C) = PowerSeries.C (C.u : R) * ((D W X - PowerSeries.C C.r * D W (wSer W)) * vv W C
      + (X - PowerSeries.C C.r * wSer W) * D W (vv W C)) := by
    simp only [phi, map_sub, Derivation.leibniz, smul_eq_mul, D_C]
    ring
  rw [hphiD, hvD, hdenD, hDX, hDw, hfwsub]
  have hw := (CurveSer.wSer_fixed W).2
  have h := flow_vc (PowerSeries.C W.a₁) (PowerSeries.C W.a₂) (PowerSeries.C W.a₃) (PowerSeries.C W.a₄)
    (PowerSeries.C W.a₆) (PowerSeries.C (C.u : R)) (PowerSeries.C ((C.u⁻¹ : Rˣ) : R)) (PowerSeries.C C.r)
    (PowerSeries.C C.s) (PowerSeries.C C.t) X (wSer W) (vv W C) hw (hv_C W C) (hU_C C)
  simp only [phi, psi, fw, fu, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆,
    map_mul, map_add, map_sub, map_pow, map_ofNat] at h ⊢
  linear_combination h

end Ring

section Subst

variable {R : Type} [CommRing R]

theorem cc_subst0 {f a : R⟦X⟧} (ha : constantCoeff a = 0) (hf : constantCoeff f = 0) :
    constantCoeff (f.subst a) = 0 :=
  constantCoeff_subst_eq_zero ha f hf

theorem subst_C' {s : R⟦X⟧} (hs0 : constantCoeff s = 0) (a : R) : (PowerSeries.C a).subst s = PowerSeries.C a := by
  rw [← ISer.subHom_apply _ hs0, ISer.subHom_C]

end Subst

section Field

variable {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)

theorem derivative_C_mul' (a : K) (f : K⟦X⟧) :
    derivative K (PowerSeries.C a * f) = PowerSeries.C a * derivative K f := by
  rw [Derivation.leibniz, derivative_C, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]

theorem log_phi : (logSer (C • W)).subst (phi W C) = PowerSeries.C (C.u : K) * logSer W := by
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have h1 : derivative K (phi W C) * fw W = PowerSeries.C (C.u : K) * (fw (C • W)).subst (phi W C) := by
    rw [← D_phi, CurveSer.D_apply, mul_comm]
  have h2 : (fw (C • W)).subst (phi W C) * (om (C • W)).subst (phi W C) = 1 := by
    rw [← subst_mul hs, CurveSer.fw_mul_om, ← coe_substAlgHom hs, map_one]
  have h3 := CurveSer.fw_mul_om W
  have hd : derivative K ((logSer (C • W)).subst (phi W C)) = PowerSeries.C (C.u : K) * om W := by
    rw [derivative_subst hs, (logSpec K (C • W)).2.2.1]
    linear_combination (-((om (C • W)).subst (phi W C) * derivative K (phi W C))) * h3
      + ((om (C • W)).subst (phi W C) * om W) * h1 + (PowerSeries.C (C.u : K) * om W) * h2
  have hc : constantCoeff ((logSer (C • W)).subst (phi W C)) = 0 :=
    cc_subst0 (phi_cc W C) (logSpec K (C • W)).1
  have hd2 : derivative K (PowerSeries.C (C.u : K) * logSer W) = PowerSeries.C (C.u : K) * om W := by
    rw [derivative_C_mul', (logSpec K W).2.2.1]
  have hc2 : constantCoeff (PowerSeries.C (C.u : K) * logSer W) = 0 := by
    simp [(logSpec K W).1]
  rw [(integSpec K _).2.2 _ hc hd, (integSpec K _).2.2 _ hc2 hd2]

theorem cUi_cc : constantCoeff (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X) = 0 := by simp

theorem exp_eq : expSer (C • W) =
    (phi W C).subst ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X)) := by
  have hm0 := cUi_cc C
  have hmS : HasSubst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X) := HasSubst.of_constantCoeff_zero' hm0
  have he := expSpec K W
  have heS : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' he.1
  have hh0 : constantCoeff ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X)) = 0 := cc_subst0 hm0 he.1
  have hhS := HasSubst.of_constantCoeff_zero' hh0
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have hlog : (logSer (C • W)).subst ((phi W C).subst ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X))) = X := by
    rw [← subst_comp_subst_apply hs hhS, log_phi, subst_mul hhS, subst_C' hh0,
      ← subst_comp_subst_apply heS hmS, he.2.2.1, subst_X hmS, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  have hl := logSpec K (C • W)
  have hsp := compInvSpec K (logSer (C • W)) hl.1 (by rw [hl.2.1]; exact isUnit_one)
  exact (hsp.2.2.2.2.1 _ (cc_subst0 hh0 (phi_cc W C)) hlog).symm

theorem mulBy_eq (c : K) : Formalism.L2.Th1.C.mulBy (logSer (C • W)) (expSer (C • W)) c =
    (phi W C).subst ((Formalism.L2.Th1.C.mulBy (logSer W) (expSer W) c).subst (compInv (phi W C))) := by
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have hci := compInvSpec K (phi W C) (phi_cc W C) (by rw [phi_coeff_one]; exact Units.isUnit _)
  have hp0 : constantCoeff (compInv (phi W C)) = 0 := hci.1
  have hpS : HasSubst (compInv (phi W C)) := HasSubst.of_constantCoeff_zero' hp0
  have hl := logSpec K W
  have he := expSpec K W
  have heS : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' he.1
  have hl' : logSer (C • W) = PowerSeries.C (C.u : K) * (logSer W).subst (compInv (phi W C)) := by
    have h := congrArg (fun f : K⟦X⟧ => f.subst (compInv (phi W C))) (log_phi W C)
    rw [subst_comp_subst_apply hs hpS, hci.2.1, X_subst, subst_mul hpS, subst_C' hp0] at h
    exact h
  have hq0 : constantCoeff (PowerSeries.C c * logSer (C • W)) = 0 := by
    simp [(logSpec K (C • W)).1]
  have hqS : HasSubst (PowerSeries.C c * logSer (C • W)) := HasSubst.of_constantCoeff_zero' hq0
  have hm0 := cUi_cc C
  have hmS : HasSubst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X) := HasSubst.of_constantCoeff_zero' hm0
  have hh0 : constantCoeff ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X)) = 0 := cc_subst0 hm0 he.1
  have hhS := HasSubst.of_constantCoeff_zero' hh0
  have hr0 : constantCoeff (PowerSeries.C c * logSer W) = 0 := by simp [hl.1]
  have hrS : HasSubst (PowerSeries.C c * logSer W) := HasSubst.of_constantCoeff_zero' hr0
  unfold Formalism.L2.Th1.C.mulBy
  rw [exp_eq, subst_comp_subst_apply hhS hqS, subst_comp_subst_apply hmS hqS, subst_mul hqS, subst_C' hq0,
    subst_X hqS, subst_comp_subst_apply hrS hpS, subst_mul hpS, subst_C' hp0, hl']
  congr 2
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (((C.u⁻¹ : Kˣ) : K)) c, mul_assoc c,
    Units.inv_mul, mul_one]

end Field

section Integral

open Formalism.L2.Th1.C

variable {K : Type} [Field K] [CharZero K] (R' : Subring K)

theorem intPS_C' {a : K} (ha : a ∈ R') : IntPS R' (PowerSeries.C a) := by
  intro n; rw [coeff_C]; split_ifs; exacts [ha, R'.zero_mem]

theorem intPS_X' : IntPS R' (X : K⟦X⟧) := by
  intro n; rw [coeff_X]; split_ifs; exacts [R'.one_mem, R'.zero_mem]

theorem intPS_add' {f g : K⟦X⟧} (hf : IntPS R' f) (hg : IntPS R' g) : IntPS R' (f + g) := by
  intro n; rw [map_add]; exact R'.add_mem (hf n) (hg n)

theorem intPS_sub' {f g : K⟦X⟧} (hf : IntPS R' f) (hg : IntPS R' g) : IntPS R' (f - g) := by
  intro n; rw [map_sub]; exact R'.sub_mem (hf n) (hg n)

theorem intPS_mul' {f g : K⟦X⟧} (hf : IntPS R' f) (hg : IntPS R' g) : IntPS R' (f * g) := by
  intro n; rw [coeff_mul]; exact R'.sum_mem fun p _ => R'.mul_mem (hf _) (hg _)

theorem intPS_wSer {W : WeierstrassCurve K} (hW : CoeffIn R' W) : IntPS R' (wSer W) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  let WS : WeierstrassCurve R' := ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩, ⟨_, h4⟩, ⟨_, h6⟩⟩
  have e : WS.map R'.subtype = W := by ext <;> rfl
  intro n
  rw [← e, ← (seriesMap R' K R'.subtype WS).1, coeff_map]
  exact SetLike.coe_mem _

theorem intPS_subst' {f a : K⟦X⟧} (hf : IntPS R' f) (ha : IntPS R' a) (ha0 : constantCoeff a = 0) :
    IntPS R' (f.subst a) :=
  Pts.intPS_of_intMv (IntegralMvPolynomialLemmas.intMv_subst hf ⟨ha0, Pts.intMv_of_intPS ha⟩)

theorem intPS_compInv {f : K⟦X⟧} (hf : IntPS R' f) (h0 : constantCoeff f = 0) {u ui : K} (hui : ui ∈ R')
    (h1 : coeff 1 f = u) (huu : u * ui = 1) : IntPS R' (compInv f) := by
  let fS : R'⟦X⟧ := PowerSeries.mk fun n => ⟨coeff n f, hf n⟩
  have e : PowerSeries.map R'.subtype fS = f := by
    ext n; simp [fS]
  have h0S : constantCoeff fS = 0 := by
    apply Subtype.ext
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [fS, h0]
  have hm : coeff 1 fS * ⟨ui, hui⟩ = 1 := Subtype.ext (by simp [fS, h1, huu])
  have h1S : IsUnit (coeff 1 fS) := ⟨⟨_, ⟨ui, hui⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  intro n
  rw [← e, ← compInvMap R' K R'.subtype fS h0S h1S, coeff_map]
  exact SetLike.coe_mem _

variable {R'}

theorem intPS_phi (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R') : IntPS R' (phi W C) := by
  have hw := intPS_wSer R' hW
  have hden : IntPS R' (den W C) :=
    intPS_add' R' (intPS_add' R' (intPS_C' R' R'.one_mem) (intPS_mul' R' (intPS_C' R' hs) (intPS_X' R')))
      (intPS_mul' R' (intPS_C' R' (R'.sub_mem ht (R'.mul_mem hs hr))) hw)
  have hv : IntPS R' (vv W C) :=
    Pts.intPS_of_intMv (IntegralMvPolynomialLemmas.intMv_of_mul_eq_one (Pts.intMv_of_intPS hden) (den_cc W C) (den_mul_vv W C))
  exact intPS_mul' R' (intPS_mul' R' (intPS_C' R' hu) (intPS_sub' R' (intPS_X' R') (intPS_mul' R' (intPS_C' R' hr) hw))) hv

theorem endInt_varChange (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hu' : ((C.u⁻¹ : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R')
    (c : K) (h : EndInt R' (logSer W) (expSer W) c) : EndInt R' (logSer (C • W)) (expSer (C • W)) c := by
  unfold EndInt at h ⊢
  rw [mulBy_eq]
  have hphi := intPS_phi W hW C hu hr hs ht
  have hci := compInvSpec K (phi W C) (phi_cc W C) (by rw [phi_coeff_one]; exact Units.isUnit _)
  have hpinv := intPS_compInv R' hphi (phi_cc W C) hu' (phi_coeff_one W C) (Units.mul_inv C.u)
  have hm0 : constantCoeff (Formalism.L2.Th1.C.mulBy (logSer W) (expSer W) c) = 0 :=
    cc_subst0 (by simp [(logSpec K W).1]) (expSpec K W).1
  exact intPS_subst' R' hphi (intPS_subst' R' h hpinv hci.1) (cc_subst0 hci.1 hm0)

end Integral

end Formalism.L2.KerInert.VC
