import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.StatementModel
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FormalGroupLawFirstHalfHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.ExpLog
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

open PowerSeries

noncomputable section

namespace Formalism.L2.KerInert.MC

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

end Formalism.L2.KerInert.MC

namespace Formalism.L2.KerInert.ModelP

open NumberField Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

section Norms

variable {p : ℕ} [Fact p.Prime]

abbrev RB (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := Formalism.G.unitBall ℂ_[p]

theorem norm_two_three (h5 : 5 ≤ p) : ‖(2 : ℂ_[p])‖ = 1 ∧ ‖(3 : ℂ_[p])‖ = 1 := by
  have n2 : ¬ (p : ℤ) ∣ 2 := fun h => by have := Int.le_of_dvd (by norm_num) h; omega
  have n3 : ¬ (p : ℤ) ∣ 3 := fun h => by have := Int.le_of_dvd (by norm_num) h; omega
  have e2 := Formalism.MainNotions.Ext.CutA.norm_int_cp_eq_one (p := p) 2 n2
  have e3 := Formalism.MainNotions.Ext.CutA.norm_int_cp_eq_one (p := p) 3 n3
  push_cast at e2 e3
  exact ⟨e2, e3⟩

theorem nadd {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem nneg {x : ℂ_[p]} (hx : ‖x‖ ≤ 1) : ‖-x‖ ≤ 1 := by rwa [norm_neg]

theorem nmul {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem vc_gen (h5 : 5 ≤ p) (W : WeierstrassCurve ℂ_[p]) (j1 : ‖W.a₁‖ ≤ 1) (j2 : ‖W.a₂‖ ≤ 1) (j3 : ‖W.a₃‖ ≤ 1)
    (hΔ0 : ‖W.Δ‖ = 1) (C : WeierstrassCurve.VariableChange ℂ_[p]) (i1 : ‖(C • W).a₁‖ ≤ 1)
    (i2 : ‖(C • W).a₂‖ ≤ 1) (i3 : ‖(C • W).a₃‖ ≤ 1) (hΔ : ‖(C • W).Δ‖ = 1) :
    ‖((C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ ‖C.r‖ ≤ 1 ∧ ‖C.s‖ ≤ 1 ∧ ‖C.t‖ ≤ 1 := by
  obtain ⟨t2, t3⟩ := norm_two_three (p := p) h5
  rw [WeierstrassCurve.variableChange_Δ, norm_mul, norm_pow, hΔ0, mul_one] at hΔ
  have hui : ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hΔ
  have e : ((C.u : ℂ_[p]ˣ) : ℂ_[p]) * ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = 1 := Units.mul_inv C.u
  have hu : ‖((C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
    have := congrArg norm e
    rwa [norm_mul, hui, mul_one, norm_one] at this
  have h2 : (2 : ℂ_[p]) ≠ 0 := by intro h; rw [h, norm_zero] at t2; exact zero_ne_one t2
  have h3 : (3 : ℂ_[p]) ≠ 0 := by intro h; rw [h, norm_zero] at t3; exact zero_ne_one t3
  set U : ℂ_[p] := ((C.u : ℂ_[p]ˣ) : ℂ_[p]) with hU
  set Ui : ℂ_[p] := ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hUi
  have es' : U * (C • W).a₁ - W.a₁ = 2 * C.s := by
    rw [WeierstrassCurve.variableChange_a₁]
    linear_combination (W.a₁ + 2 * C.s) * e
  have hs : ‖C.s‖ ≤ 1 := by
    have es : C.s = (U * (C • W).a₁ - W.a₁) / 2 := by rw [eq_div_iff h2, es']; ring
    rw [es, norm_div, t2, div_one, sub_eq_add_neg]
    exact nadd (nmul hu.le i1) (nneg j1)
  have et' : U ^ 3 * (C • W).a₃ - W.a₃ - C.r * W.a₁ = 2 * C.t := by
    rw [WeierstrassCurve.variableChange_a₃]
    linear_combination ((W.a₃ + C.r * W.a₁ + 2 * C.t) * ((U * Ui) ^ 2 + U * Ui + 1)) * e
  have er' : U ^ 2 * (C • W).a₂ - W.a₂ + C.s * W.a₁ + C.s ^ 2 = 3 * C.r := by
    rw [WeierstrassCurve.variableChange_a₂]
    linear_combination ((W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * (U * Ui + 1)) * e
  have hr : ‖C.r‖ ≤ 1 := by
    have er : C.r = (U ^ 2 * (C • W).a₂ - W.a₂ + C.s * W.a₁ + C.s ^ 2) / 3 := by rw [eq_div_iff h3, er']; ring
    rw [er, norm_div, t3, div_one, sub_eq_add_neg]
    refine nadd (nadd (nadd (nmul ?_ i2) (nneg j2)) (nmul hs j1)) ?_
    · rw [norm_pow, hu, one_pow]
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hs
  have ht : ‖C.t‖ ≤ 1 := by
    have et : C.t = (U ^ 3 * (C • W).a₃ - W.a₃ - C.r * W.a₁) / 2 := by rw [eq_div_iff h2, et']; ring
    rw [et, norm_div, t2, div_one, sub_eq_add_neg, sub_eq_add_neg]
    refine nadd (nadd (nmul ?_ i3) (nneg j3)) (nneg (nmul hr j1))
    rw [norm_pow, hu, one_pow]
  exact ⟨hu, hui, hr, hs, ht⟩

end Norms

section G

variable {p : ℕ} [Fact p.Prime]

theorem mulBy_g (g : G1 p) (hOk : g.Ok) (c : ℂ_[p]) :
    (g.mulBy c (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) c := by
  have hl : g.l = Formalism.L2.Th1.A.logSer g.W := Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1
  have he : g.ex = Formalism.L2.Th1.A.expSer g.W := Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk
  unfold G1.mulBy G1.pt G1.lg Formalism.L2.Th1.C.mulBy
  rw [← hl, ← he]
  have hx : (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) g.l : MvPowerSeries Unit ℂ_[p]) = g.l :=
    PowerSeries.X_subst g.l
  rw [hx]
  rfl

theorem coeffIn_g (g : G1 p) (hOk : g.Ok) : Formalism.L2.Th1.C.CoeffIn (RB p) g.W := by
  obtain ⟨⟨h1, h2, h3, h4, h6, -⟩, -⟩ := hOk
  exact ⟨h1, h2, h3, h4, h6⟩

theorem g_W_eq (g g' : G1 p) (hl : g.lam = g'.lam) (hL : g.abelian₂ = g'.abelian₂) :
    g.W = (g.C * g'.C⁻¹) • g'.W := by
  unfold G1.W; rw [hl, hL, mul_smul, inv_smul_smul]

theorem vc_pair (h5 : 5 ≤ p) (g g' : G1 p) (hOk : g.Ok) (hOk' : g'.Ok) (hl : g.lam = g'.lam) (hL : g.abelian₂ = g'.abelian₂) :
    let C := g.C * g'.C⁻¹
    ‖((C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ ‖C.r‖ ≤ 1 ∧ ‖C.s‖ ≤ 1 ∧ ‖C.t‖ ≤ 1 := by
  intro C
  have hW := g_W_eq g g' hl hL
  obtain ⟨i1, i2, i3, -, -, hΔ⟩ := hOk.1
  obtain ⟨j1, j2, j3, -, -, hΔ'⟩ := hOk'.1
  refine vc_gen h5 g'.W j1 j2 j3 hΔ' C ?_ ?_ ?_ ?_
  · show ‖(C • g'.W).a₁‖ ≤ 1
    rw [← hW]; exact i1
  · show ‖(C • g'.W).a₂‖ ≤ 1
    rw [← hW]; exact i2
  · show ‖(C • g'.W).a₃‖ ≤ 1
    rw [← hW]; exact i3
  · show ‖(C • g'.W).Δ‖ = 1
    rw [← hW]; exact hΔ

end G

section EndInt

variable {p : ℕ} [Fact p.Prime]

theorem endIntInertAll_of (hE : EndIntInert) (hG : GenusOneWittExists) : EndIntInertAll := by
  intro D p _ cc δ g hA h5 hIn α hα
  obtain ⟨hcurve, hcop, hδ, hLam, hOk⟩ := hA
  obtain ⟨g', hl, hA', hW'⟩ := hG D cc δ hcurve hδ p hcop h5 hIn g.lam
  have hOk' : g'.Ok := hA'.2.2.2.2
  have hL : g.abelian₂ = g'.abelian₂ := hLam.trans hA'.2.2.2.1.symm
  have hα' : α ∈ OKp D g'.lam := by rw [hl]; exact hα
  have h1 := hE D p cc δ g' hA' h5 hIn hW' α hα'
  have hE' : Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g'.W) (Formalism.L2.Th1.A.expSer g'.W) α.1 := by
    unfold Formalism.L2.Th1.C.EndInt
    rw [← mulBy_g g' hOk']
    intro n
    exact h1 (Finsupp.single () n)
  obtain ⟨hu, hui, hr, hs, ht⟩ := vc_pair h5 g g' hOk hOk' hl.symm hL
  have hEg : Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) α.1 := by
    rw [g_W_eq g g' hl.symm hL]
    exact Formalism.L2.KerInert.MC.endInt_varChange _ (coeffIn_g g' hOk') _ hu.le hui.le hr hs ht _ hE'
  rw [mulBy_g g hOk α.1]
  intro n
  exact Formalism.L2.Th1.C.Pts.intMv_of_intPS hEg n

end EndInt

end Formalism.L2.KerInert.ModelP

namespace Formalism.L2.KerInert.ModelP

open NumberField Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.L2.Th1.A

section Ph

variable {p : ℕ} [Fact p.Prime]

theorem integral_iff' {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) :
    IntegralMv F ↔ ∃ G : MvPowerSeries σ (RB p), MvPowerSeries.map (RB p).subtype G = F := by
  constructor
  · intro h
    refine ⟨fun e => ⟨MvPowerSeries.coeff e F, h e⟩, ?_⟩
    ext e
    rfl
  · rintro ⟨G, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e G).2

theorem integral_subst' {σ τ : Type*} [Finite σ] (a : σ → MvPowerSeries τ ℂ_[p])
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (haI : ∀ i, IntegralMv (a i))
    {f : MvPowerSeries σ ℂ_[p]} (hf : IntegralMv f) : IntegralMv (MvPowerSeries.subst a f) := by
  choose a' ha' using fun i => (integral_iff' (a i)).1 (haI i)
  obtain ⟨f', rfl⟩ := (integral_iff' f).1 hf
  have h0 : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0 := by
    intro i
    apply Subtype.ext
    have e : ((MvPowerSeries.constantCoeff (a' i) : RB p) : ℂ_[p]) =
        MvPowerSeries.constantCoeff (MvPowerSeries.map (RB p).subtype (a' i)) := by
      rw [MvPowerSeries.constantCoeff_map]; rfl
    rw [e, ha', ha0]
    rfl
  have hs : MvPowerSeries.HasSubst a' := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  refine (integral_iff' _).2 ⟨MvPowerSeries.subst a' f', ?_⟩
  rw [MvPowerSeries.map_subst hs]
  simp only [ha']

theorem integral_psubst {σ : Type*} {y : MvPowerSeries σ ℂ_[p]} (hy0 : MvPowerSeries.constantCoeff y = 0)
    (hyI : IntegralMv y) {f : PowerSeries ℂ_[p]} (hf : IntegralMv (f : MvPowerSeries Unit ℂ_[p])) :
    IntegralMv (PowerSeries.subst y f) :=
  integral_subst' (fun _ : Unit => y) (fun _ => hy0) (fun _ => hyI) hf

theorem cc_subst_keep {a f : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) :
    constantCoeff (PowerSeries.subst a f) = constantCoeff f := by
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const f]
  rw [← ISer.subHom_apply _ ha, map_add, map_mul, ISer.subHom_X, ISer.subHom_C]
  simp [ha]

theorem X_mul_shift (F : PowerSeries ℂ_[p]) (ep : ℂ_[p]) :
    (X : PowerSeries ℂ_[p]) * PowerSeries.mk (fun n => ep⁻¹ * coeff (n + 1) F) =
      PowerSeries.C (ep⁻¹) * (F - PowerSeries.C (constantCoeff F)) := by
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_mk, coeff_C_mul, map_sub, coeff_C]
    simp

abbrev Fg (g : G1 p) : PowerSeries ℂ_[p] :=
  PowerSeries.subst (PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * logSer g.W) (sgSer g.lam g.abelian₂)

theorem ePhi1_X (g : G1 p) (hOk : g.Ok) :
    (X : PowerSeries ℂ_[p]) * ePhi1 g.lam g.abelian₂ g.C g.wq =
      PowerSeries.C ((((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))⁻¹) * (Fg g - PowerSeries.C (constantCoeff (Fg g))) := by
  have hl : flog (g.C • wModel g.lam g.abelian₂) g.wq = logSer g.W :=
    Formalism.L2.KerInert.Dict.formal_logarithm_agree p _ g.wq hOk.2.1
  rw [← X_mul_shift]
  refine congrArg (fun E : PowerSeries ℂ_[p] => (X : PowerSeries ℂ_[p]) * E) ?_
  ext n
  simp only [ePhi1, coeff_mk, PowerSeries.algebraMap_eq, hl]

theorem sCf {σ : Type*} (s : MvPowerSeries σ ℂ_[p]) (hs : MvPowerSeries.constantCoeff s = 0) (u : ℂ_[p])
    (f : PowerSeries ℂ_[p]) :
    PowerSeries.subst s (PowerSeries.C u * f) = MvPowerSeries.C u * PowerSeries.subst s f := by
  rw [PowerSeries.subst_mul (HasSubst.of_constantCoeff_zero hs), PowerSeries.subst_C]

theorem sCX {σ : Type*} (s : MvPowerSeries σ ℂ_[p]) (hs : MvPowerSeries.constantCoeff s = 0) (u : ℂ_[p]) :
    PowerSeries.subst s (PowerSeries.C u * X) = MvPowerSeries.C u * s := by
  rw [sCf s hs, PowerSeries.subst_X (HasSubst.of_constantCoeff_zero hs)]

theorem mvC_eq (a : ℂ_[p]) : (MvPowerSeries.C a : MvPowerSeries Unit ℂ_[p]) = PowerSeries.C a := rfl

theorem hs0 {σ : Type*} {s : MvPowerSeries σ ℂ_[p]} (hs : MvPowerSeries.constantCoeff s = 0) : HasSubst s :=
  HasSubst.of_constantCoeff_zero hs

theorem hs1 {s : PowerSeries ℂ_[p]} (hs : constantCoeff s = 0) : HasSubst s :=
  HasSubst.of_constantCoeff_zero' hs

theorem change (h5 : 5 ≤ p) (g g' : G1 p) (hOk : g.Ok) (hOk' : g'.Ok) (hl : g'.lam = g.lam) (hL : g'.abelian₂ = g.abelian₂)
    (hE1 : constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    (hE1' : constantCoeff (ePhi1 g'.lam g'.abelian₂ g'.C g'.wq) = 1) :
    ∃ φ : PowerSeries ℂ_[p], constantCoeff φ = 0 ∧ IntegralMv (φ : MvPowerSeries Unit ℂ_[p]) ∧
      (∀ (σ : Type) (y : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff y = 0 → ∀ c : ℂ_[p],
          PowerSeries.subst (g.mulBy c y) φ = g'.mulBy c (PowerSeries.subst y φ)) ∧
      (∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
          MvPowerSeries.constantCoeff b = 0 →
          PowerSeries.subst (g.add a b) φ = g'.add (PowerSeries.subst a φ) (PowerSeries.subst b φ)) ∧
      ∃ h : PowerSeries ℂ_[p], constantCoeff h = 0 ∧ IntegralMv (expMv (h : MvPowerSeries Unit ℂ_[p])) ∧
        PowerSeries.subst φ g'.ph = g.ph + h := by
  set C21 := g'.C * g.C⁻¹ with hC21
  have hW : g'.W = C21 • g.W := g_W_eq g' g hl hL
  obtain ⟨hu, hui, hr, hs, ht⟩ := vc_pair h5 g' g hOk' hOk hl hL
  set u : ℂ_[p] := ((C21.u : ℂ_[p]ˣ) : ℂ_[p]) with hu_def
  set φ : PowerSeries ℂ_[p] := Formalism.L2.KerInert.MC.phi g.W C21 with hφ_def
  have hφ0 : constantCoeff φ = 0 := Formalism.L2.KerInert.MC.phi_cc g.W C21
  have hφ1 : coeff 1 φ = u := Formalism.L2.KerInert.MC.phi_coeff_one g.W C21
  have hφI' : Formalism.L2.Th1.C.IntPS (RB p) φ :=
    Formalism.L2.KerInert.MC.intPS_phi g.W (coeffIn_g g hOk) C21 hu.le hr hs ht
  have hφI : IntegralMv (φ : MvPowerSeries Unit ℂ_[p]) := fun n => Formalism.L2.Th1.C.Pts.intMv_of_intPS hφI' n
  have hlg : g.l = logSer g.W := Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1
  have hlg' : g'.l = logSer g'.W := Formalism.L2.KerInert.Dict.formal_logarithm_agree p g'.W g'.wq hOk'.2.1
  have hexg : g.ex = expSer g.W := Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk
  have hexg' : g'.ex = expSer g'.W := Formalism.L2.KerInert.Dict.formal_exponential_agree p g' hOk'
  have hl0 : constantCoeff (logSer g.W) = 0 := (logSpec ℂ_[p] g.W).1
  have hl0' : constantCoeff (logSer g'.W) = 0 := (logSpec ℂ_[p] g'.W).1
  have he0 : constantCoeff (expSer g.W) = 0 := (expSpec ℂ_[p] g.W).1
  have he0' : constantCoeff (expSer g'.W) = 0 := (expSpec ℂ_[p] g'.W).1

  have hlog : PowerSeries.subst φ (logSer g'.W) = PowerSeries.C u * logSer g.W := by
    rw [hW]; exact Formalism.L2.KerInert.MC.log_phi g.W C21

  have hCX : constantCoeff (PowerSeries.C u * X : PowerSeries ℂ_[p]) = 0 := by simp
  have hCXi : constantCoeff (PowerSeries.C (((C21.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * X : PowerSeries ℂ_[p]) = 0 := by simp
  have hinner : PowerSeries.subst (PowerSeries.C u * X : PowerSeries ℂ_[p])
      (PowerSeries.C (((C21.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * X : PowerSeries ℂ_[p]) = X := by
    rw [sCX _ hCX, mvC_eq, ← mul_assoc, ← map_mul]
    rw [show (((C21.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * u = 1 from Units.inv_mul C21.u]
    simp
  have hexp : PowerSeries.subst (expSer g.W) φ = PowerSeries.subst (PowerSeries.C u * X : PowerSeries ℂ_[p]) (expSer g'.W) := by
    have he := Formalism.L2.KerInert.MC.exp_eq g.W C21
    rw [← hW] at he
    have h1 : constantCoeff (PowerSeries.subst (PowerSeries.C (((C21.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * X : PowerSeries ℂ_[p]) (expSer g.W)) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hCXi _ he0
    rw [he, PowerSeries.subst_comp_subst_apply (hs1 h1) (hs1 hCX),
      PowerSeries.subst_comp_subst_apply (hs1 hCXi) (hs1 hCX), hinner, PowerSeries.X_subst]

  have hpt : ∀ (σ : Type) (s : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff s = 0 →
      PowerSeries.subst (PowerSeries.subst s g.ex) φ = PowerSeries.subst (MvPowerSeries.C u * s) g'.ex := by
    intro σ s hs
    rw [hexg, hexg', ← PowerSeries.subst_comp_subst_apply (hs1 he0) (hs0 hs), hexp,
      PowerSeries.subst_comp_subst_apply (hs1 hCX) (hs0 hs), sCX s hs]
  have hlgs : ∀ (σ : Type) (y : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff y = 0 →
      PowerSeries.subst (PowerSeries.subst y φ) g'.l = MvPowerSeries.C u * PowerSeries.subst y g.l := by
    intro σ y hy
    rw [hlg', hlg, ← PowerSeries.subst_comp_subst_apply (hs1 hφ0) (hs0 hy), hlog, sCf y hy]
  have hlgcc : ∀ (σ : Type) (y : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff y = 0 →
      MvPowerSeries.constantCoeff (PowerSeries.subst y g.l) = 0 := by
    intro σ y hy
    rw [hlg]; exact PowerSeries.constantCoeff_subst_eq_zero hy _ hl0
  have hφy : ∀ (σ : Type) (y : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff y = 0 →
      MvPowerSeries.constantCoeff (PowerSeries.subst y φ) = 0 :=
    fun σ y hy => PowerSeries.constantCoeff_subst_eq_zero hy _ hφ0
  refine ⟨φ, hφ0, hφI, ?_, ?_, ?_⟩
  · intro σ y hy c
    have hs : MvPowerSeries.constantCoeff (MvPowerSeries.C c * PowerSeries.subst y g.l) = 0 := by
      rw [map_mul, hlgcc σ y hy, mul_zero]
    unfold G1.mulBy G1.pt G1.lg
    rw [hpt σ _ hs, hlgs σ y hy]
    congr 1
    ring
  · intro σ a b ha hb
    have hs : MvPowerSeries.constantCoeff (PowerSeries.subst a g.l + PowerSeries.subst b g.l) = 0 := by
      rw [map_add, hlgcc σ a ha, hlgcc σ b hb, add_zero]
    unfold G1.add G1.pt G1.lg
    rw [hpt σ _ hs, hlgs σ a ha, hlgs σ b hb]
    congr 1
    ring
  · set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
    set ε' : ℂ_[p] := ((g'.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε'
    have hu0 : u ≠ 0 := Units.ne_zero _
    have hε0 : ε ≠ 0 := Units.ne_zero _
    have hε0' : ε' ≠ 0 := Units.ne_zero _
    have hCC : g'.C = C21 * g.C := by rw [hC21, inv_mul_cancel_right]
    have hεε : ε' * u = ε := by
      have e : ((g'.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * ((C21.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) := by
        rw [hCC]
        show (((C21.u * g.C.u)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = _
        rw [mul_inv_rev, Units.val_mul]
      rw [hε', e, mul_assoc, hu_def, Units.inv_mul, mul_one]
    have hεi : u * ε⁻¹ = ε'⁻¹ := by
      rw [← hεε]; field_simp
    have hA0 : constantCoeff (PowerSeries.C ε' * logSer g'.W) = 0 := by simp [hl0']
    have hin : PowerSeries.subst φ (PowerSeries.C ε' * logSer g'.W) = PowerSeries.C ε * logSer g.W := by
      rw [sCf φ hφ0, hlog, mvC_eq, ← mul_assoc, ← map_mul, hεε]
    have hFgg : PowerSeries.subst φ (Fg g') = Fg g := by
      show PowerSeries.subst φ (PowerSeries.subst (PowerSeries.C ε' * logSer g'.W) (sgSer g'.lam g'.abelian₂)) =
        PowerSeries.subst (PowerSeries.C ε * logSer g.W) (sgSer g.lam g.abelian₂)
      rw [hl, hL, PowerSeries.subst_comp_subst_apply (hs1 hA0) (hs1 hφ0), hin]
    have hcc : constantCoeff (Fg g') = constantCoeff (Fg g) := by rw [← hFgg, cc_subst_keep hφ0]
    set E := ePhi1 g.lam g.abelian₂ g.C g.wq with hE
    set E' := ePhi1 g'.lam g'.abelian₂ g'.C g'.wq with hE'
    have hX : (X : PowerSeries ℂ_[p]) * E = PowerSeries.C (ε⁻¹) * (Fg g - PowerSeries.C (constantCoeff (Fg g))) :=
      ePhi1_X g hOk
    have hX' : (X : PowerSeries ℂ_[p]) * E' =
        PowerSeries.C (ε'⁻¹) * (Fg g' - PowerSeries.C (constantCoeff (Fg g'))) := ePhi1_X g' hOk'
    set Es : PowerSeries ℂ_[p] := PowerSeries.subst φ E' with hEs
    have hkey : φ * Es = PowerSeries.C u * ((X : PowerSeries ℂ_[p]) * E) := by
      have e1 : PowerSeries.subst φ ((X : PowerSeries ℂ_[p]) * E') = φ * Es := by
        rw [PowerSeries.subst_mul (hs1 hφ0), PowerSeries.subst_X (hs1 hφ0)]
      rw [← e1, hX', PowerSeries.subst_mul (hs1 hφ0), Formalism.L2.KerInert.MC.subst_C' hφ0,
        PowerSeries.subst_sub (hs1 hφ0), hFgg, Formalism.L2.KerInert.MC.subst_C' hφ0, hcc, hX, ← mul_assoc, ← map_mul, hεi]
    set q : PowerSeries ℂ_[p] := PowerSeries.mk fun n => coeff (n + 1) φ with hq
    have hφq : φ = (X : PowerSeries ℂ_[p]) * q := by
      have e := PowerSeries.eq_X_mul_shift_add_const φ
      rw [hφ0, map_zero, add_zero] at e
      exact e
    have hqE : q * Es = PowerSeries.C u * E := by
      have e : (X : PowerSeries ℂ_[p]) * (q * Es) = X * (PowerSeries.C u * E) := by
        rw [← mul_assoc, ← hφq, hkey]; ring
      exact mul_left_cancel₀ PowerSeries.X_ne_zero e
    set Q : PowerSeries ℂ_[p] := PowerSeries.C (((C21.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * q with hQ
    have hQE : Q * Es = E := by
      rw [hQ, mul_assoc, hqE, ← mul_assoc, ← map_mul,
        show (((C21.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * u = 1 from Units.inv_mul C21.u, map_one, one_mul]
    have hQI' : Formalism.L2.Th1.C.IntPS (RB p) Q := by
      intro n
      rw [hQ, coeff_C_mul, hq, coeff_mk]
      exact nmul hui.le (hφI' (n + 1))
    have hQI : IntegralMv (Q : MvPowerSeries Unit ℂ_[p]) := fun n => Formalism.L2.Th1.C.Pts.intMv_of_intPS hQI' n
    have hEs1 : constantCoeff Es = 1 := by rw [hEs, cc_subst_keep hφ0, hE1']
    have hsub1 : PowerSeries.subst φ (E' - 1) = Es - 1 := by
      rw [← PowerSeries.coe_substAlgHom (hs1 hφ0), map_sub, map_one, PowerSeries.coe_substAlgHom (hs1 hφ0)]
    have hE'0 : MvPowerSeries.constantCoeff (E' - 1 : MvPowerSeries Unit ℂ_[p]) = 0 := by
      rw [map_sub, map_one]; exact sub_eq_zero.2 hE1'
    have hlogs : PowerSeries.subst φ (logMv E') = logMv Es := by
      show PowerSeries.subst φ (PI.FglShared.logS (E' : MvPowerSeries Unit ℂ_[p])) =
        PI.FglShared.logS (Es : MvPowerSeries Unit ℂ_[p])
      rw [PI.FglShared.logS_eq_subst (by exact hE1'), PI.FglShared.logS_eq_subst (by exact hEs1),
        PowerSeries.subst_comp_subst_apply (hs0 hE'0) (hs1 hφ0), hsub1]
    set h : PowerSeries ℂ_[p] := PowerSeries.subst φ g'.ph - g.ph with hh_def
    have hh : h = logMv E - logMv Es := by
      rw [hh_def]
      unfold G1.ph
      rw [← hE, ← hE', ← PowerSeries.coe_substAlgHom (hs1 hφ0), map_neg, PowerSeries.coe_substAlgHom (hs1 hφ0), hlogs]
      ring
    have hcch : constantCoeff h = 0 := by
      rw [hh, map_sub]
      have a1 := PI.FglShared.constantCoeff_logS (E : MvPowerSeries Unit ℂ_[p])
      have a2 := PI.FglShared.constantCoeff_logS (Es : MvPowerSeries Unit ℂ_[p])
      rw [show constantCoeff (logMv E) = 0 from a1, show constantCoeff (logMv Es) = 0 from a2, sub_zero]
    have hEs0 : Es ≠ 0 := by
      intro h0; rw [h0, map_zero] at hEs1; exact zero_ne_one hEs1
    have hexph : (PI.FglPhSplit.expMv (h : MvPowerSeries Unit ℂ_[p]) : PowerSeries ℂ_[p]) = Q := by
      have e1 := PI.FglShared.expMv_add' (f := (h : MvPowerSeries Unit ℂ_[p]))
        (g := PI.FglShared.logS (Es : MvPowerSeries Unit ℂ_[p])) (by exact hcch)
        (PI.FglShared.constantCoeff_logS _)
      rw [show (h : MvPowerSeries Unit ℂ_[p]) + PI.FglShared.logS (Es : MvPowerSeries Unit ℂ_[p]) =
          PI.FglShared.logS (E : MvPowerSeries Unit ℂ_[p]) by rw [hh]; show logMv E - logMv Es + logMv Es = logMv E; ring,
        PI.FglShared.expMv_logS (by exact hE1), PI.FglShared.expMv_logS (by exact hEs1)] at e1
      have e2 : (PI.FglPhSplit.expMv (h : MvPowerSeries Unit ℂ_[p]) : PowerSeries ℂ_[p]) * Es = Q * Es := by
        rw [hQE]; exact e1.symm
      exact mul_right_cancel₀ hEs0 e2
    refine ⟨h, hcch, ?_, ?_⟩
    · show IntegralMv (PI.FglPhSplit.expMv (h : MvPowerSeries Unit ℂ_[p]))
      rw [hexph]; exact hQI
    · rw [hh_def]; ring

end Ph

section Simeq

variable {p : ℕ} [Fact p.Prime]

theorem S_iff {σ : Type} (f g : MvPowerSeries σ ℂ_[p]) : Simeq f g ↔ Formalism.InvariantFactorPaths.G7.Simeq f g :=
  Formalism.L2.KerInert.Dict.formal_equivalence_agree p σ f g

theorem S_refl {σ : Type} (f : MvPowerSeries σ ℂ_[p]) : Simeq f f :=
  (S_iff _ _).2 ((Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] σ).1 f)

theorem S_symm {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq g f :=
  (S_iff _ _).2 ((Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] σ).2.1 f g ((S_iff _ _).1 h))

theorem S_trans {σ : Type} {f g k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq g k) : Simeq f k :=
  (S_iff _ _).2 ((Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] σ).2.2.1 f g k ((S_iff _ _).1 h1) ((S_iff _ _).1 h2))

theorem S_add {σ : Type} {f g f' g' : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq f' g') :
    Simeq (f + f') (g + g') :=
  (S_iff _ _).2 ((Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] σ).2.2.2.1 f g f' g' ((S_iff _ _).1 h1) ((S_iff _ _).1 h2))

theorem S_subst {σ κ : Type} [Finite σ] (s : σ → MvPowerSeries κ ℂ_[p])
    (hs0 : ∀ i, MvPowerSeries.constantCoeff (s i) = 0) (hsI : ∀ i, IntegralMv (s i))
    {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq (MvPowerSeries.subst s f) (MvPowerSeries.subst s g) :=
  (S_iff _ _).2 ((Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] σ).2.2.2.2 κ f g s hs0 (fun i n => hsI i n) ((S_iff _ _).1 h))

theorem S_of_eq {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (h : f = g) : Simeq f g := h ▸ S_refl f

theorem simeq_zero_neg {σ : Type} {H : MvPowerSeries σ ℂ_[p]} (hH : Simeq H 0) : Simeq (-H) 0 := by
  have := S_add (S_symm hH) (S_refl (-H))
  rwa [zero_add, add_neg_cancel] at this

theorem simeq_zero_add {σ : Type} {H H' : MvPowerSeries σ ℂ_[p]} (h : Simeq H 0) (h' : Simeq H' 0) : Simeq (H + H') 0 := by
  have := S_add h h'
  rwa [add_zero] at this

theorem S_int {σ : Type} {H : MvPowerSeries σ ℂ_[p]} (hH : Simeq H 0) (n : ℤ) :
    Simeq (MvPowerSeries.C (n : ℂ_[p]) * H) 0 := by
  induction n using Int.induction_on with
  | zero => exact S_of_eq (by simp)
  | succ i ih =>
    have e : MvPowerSeries.C (((i : ℤ) + 1 : ℤ) : ℂ_[p]) * H = MvPowerSeries.C ((i : ℤ) : ℂ_[p]) * H + H := by
      push_cast; rw [map_add, map_one]; ring
    rw [e]; exact simeq_zero_add ih hH
  | pred i ih =>
    have e : MvPowerSeries.C ((-(i : ℤ) - 1 : ℤ) : ℂ_[p]) * H = MvPowerSeries.C ((-(i : ℤ) : ℤ) : ℂ_[p]) * H + -H := by
      push_cast; rw [map_sub, map_one]; ring
    rw [e]; exact simeq_zero_add ih (simeq_zero_neg hH)

theorem S_small {σ : Type} {y : MvPowerSeries σ ℂ_[p]} (hy0 : MvPowerSeries.constantCoeff y = 0) (hyI : IntegralMv y)
    {h : PowerSeries ℂ_[p]} (hh0 : constantCoeff h = 0) (hhI : IntegralMv (expMv (h : MvPowerSeries Unit ℂ_[p]))) :
    Simeq (PowerSeries.subst y h) 0 := by
  refine ⟨?_, ?_⟩
  · rw [sub_zero]; exact PowerSeries.constantCoeff_subst_eq_zero hy0 _ hh0
  · rw [sub_zero]
    show IntegralMv (PI.FglPhSplit.expMv (PowerSeries.subst y h))
    rw [PI.FglShared.expMv_subst' hy0 hh0]
    exact integral_psubst hy0 hyI hhI

end Simeq

section Ops

variable {p : ℕ} [Fact p.Prime]

theorem lg_cc (g : G1 p) (hOk : g.Ok) {σ : Type*} {y : MvPowerSeries σ ℂ_[p]} (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (g.lg y) = 0 := by
  unfold G1.lg G1.l
  rw [Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1]
  exact PowerSeries.constantCoeff_subst_eq_zero hy _ (logSpec ℂ_[p] g.W).1

theorem pt_cc (g : G1 p) (hOk : g.Ok) {σ : Type*} {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (g.pt x) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hx _ hOk.2.2.1

theorem mulBy_cc (g : G1 p) (hOk : g.Ok) {σ : Type*} (c : ℂ_[p]) {y : MvPowerSeries σ ℂ_[p]}
    (hy : MvPowerSeries.constantCoeff y = 0) : MvPowerSeries.constantCoeff (g.mulBy c y) = 0 :=
  pt_cc g hOk (by rw [map_mul, lg_cc g hOk hy, mul_zero])

theorem add_cc (g : G1 p) (hOk : g.Ok) {σ : Type*} {a b : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.constantCoeff (g.add a b) = 0 :=
  pt_cc g hOk (by rw [map_add, lg_cc g hOk ha, lg_cc g hOk hb, add_zero])

theorem msubst_psubst {σ κ : Type} [Finite σ] (s : σ → MvPowerSeries κ ℂ_[p])
    (hs : ∀ i, MvPowerSeries.constantCoeff (s i) = 0) {A : MvPowerSeries σ ℂ_[p]}
    (hA : MvPowerSeries.constantCoeff A = 0) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst s (PowerSeries.subst A f) = PowerSeries.subst (MvPowerSeries.subst s A) f := by
  have hS : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs
  have hA' : PowerSeries.HasSubst A := HasSubst.of_constantCoeff_zero hA
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hA'.const hS]

variable {σ κ : Type} [Finite σ] (s : σ → MvPowerSeries κ ℂ_[p]) (hs : ∀ i, MvPowerSeries.constantCoeff (s i) = 0)
include hs

theorem msubst_lg (g : G1 p) (hOk : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst s (g.lg a) = g.lg (MvPowerSeries.subst s a) := msubst_psubst s hs ha _

theorem msubst_pt (g : G1 p) (hOk : g.Ok) {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.subst s (g.pt x) = g.pt (MvPowerSeries.subst s x) := msubst_psubst s hs hx _

theorem msubst_phAt (g : G1 p) (hOk : g.Ok) {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.subst s (g.phAt x) = g.phAt (MvPowerSeries.subst s x) := msubst_psubst s hs hx _

theorem msubst_add (g : G1 p) (hOk : g.Ok) {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (g.add a b) = g.add (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  have hS : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs
  unfold G1.add
  rw [msubst_pt s hs g hOk (by rw [map_add, lg_cc g hOk ha, lg_cc g hOk hb, add_zero]),
    ← MvPowerSeries.coe_substAlgHom hS, map_add, MvPowerSeries.coe_substAlgHom hS,
    msubst_lg s hs g hOk ha, msubst_lg s hs g hOk hb]

theorem msubst_be (g : G1 p) (hOk : g.Ok) {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (g.be a b) = g.be (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  have hS : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs
  unfold G1.be
  rw [← MvPowerSeries.coe_substAlgHom hS, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hS,
    msubst_phAt s hs g hOk (add_cc g hOk ha hb), msubst_phAt s hs g hOk ha, msubst_phAt s hs g hOk hb,
    msubst_add s hs g hOk ha hb]

end Ops

section Assembly

variable {p : ℕ} [Fact p.Prime]

theorem integral_Xv {σ : Type*} (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := by
  classical
  intro n
  show ‖MvPowerSeries.coeff n (MvPowerSeries.X i)‖ ≤ 1
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem integral_add (g : G1 p) {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hA : At D cc δ g) {σ : Type}
    {a b : MvPowerSeries σ ℂ_[p]} (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (haI : IntegralMv a) (hbI : IntegralMv b) : IntegralMv (g.add a b) := by
  have hOk : g.Ok := hA.2.2.2.2
  have hI := (Formalism.MainNotions.Ext.addInt_holds D p cc δ g hA).1
  have e := msubst_add ![a, b] (by intro i; fin_cases i <;> simpa) g hOk
    (MvPowerSeries.constantCoeff_X (0 : Fin 2)) (MvPowerSeries.constantCoeff_X (1 : Fin 2))
  have hS : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simpa)
  rw [MvPowerSeries.subst_X hS, MvPowerSeries.subst_X hS] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at e
  rw [← e]
  exact integral_subst' _ (by intro i; fin_cases i <;> simpa) (by intro i; fin_cases i <;> simpa) hI

theorem phNormOKInertAll_of (hN : PhNormOKInert) (hE : EndIntInert) (hG : GenusOneWittExists) : PhNormOKInertAll := by
  intro D p _ cc δ g hA h5 hIn a ha
  have hA0 := hA
  obtain ⟨hcurve, hcop, hδ, hLam, hOk⟩ := hA
  obtain ⟨g', hl, hA', hW'⟩ := hG D cc δ hcurve hδ p hcop h5 hIn g.lam
  have hOk' : g'.Ok := hA'.2.2.2.2
  have hL : g'.abelian₂ = g.abelian₂ := hA'.2.2.2.1.trans hLam.symm
  obtain ⟨φ, hφ0, hφI, hmul, -, h, hh0, hhI, hph⟩ := change h5 g g' hOk hOk' hl hL
    (Formalism.MainNotions.Ext.CutA.ePhiOne_holds D p cc δ g hA0) (Formalism.MainNotions.Ext.CutA.ePhiOne_holds D p cc δ g' hA')
  have hN' := hN D p cc δ g' hA' h5 hIn hW' a ha
  rw [hl] at hN'
  have hNint : tauK D g.lam (a : D.host.K) * tauKc D g.lam (a : D.host.K) = ((Algebra.norm ℤ a : ℤ) : ℂ_[p]) :=
    Formalism.MainNotions.Ext.CutA.tau_norm D g.lam a
  rw [hNint] at hN' ⊢
  set τ := tauK D g.lam (a : D.host.K) with hτ
  set N : ℤ := Algebra.norm ℤ a with hNdef
  have hX0 : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := MvPowerSeries.constantCoeff_X _
  have hXs : ∀ f : PowerSeries ℂ_[p], PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) f = f :=
    fun f => PowerSeries.X_subst f
  set M := (g.mulBy τ (Xv ()) : MvPowerSeries Unit ℂ_[p]) with hM
  have hM0 : MvPowerSeries.constantCoeff M = 0 := mulBy_cc g hOk τ hX0
  have hMI : IntegralMv M :=
    endIntInertAll_of hE hG D p cc δ g hA0 h5 hIn (τ, tauKc D g.lam (a : D.host.K)) (subset_closure ⟨a, rfl⟩)
  set M' := (g'.mulBy τ (Xv ()) : MvPowerSeries Unit ℂ_[p]) with hM'
  have hM'0 : MvPowerSeries.constantCoeff M' = 0 := mulBy_cc g' hOk' τ hX0

  have hS := S_subst (fun _ : Unit => (φ : MvPowerSeries Unit ℂ_[p])) (fun _ => hφ0) (fun _ => hφI) hN'
  have hsM' : MvPowerSeries.subst (fun _ : Unit => (φ : MvPowerSeries Unit ℂ_[p])) (g'.phAt M') =
      g.phAt M + PowerSeries.subst M h := by
    rw [msubst_phAt (fun _ : Unit => (φ : MvPowerSeries Unit ℂ_[p])) (fun _ => hφ0) g' hOk' hM'0]
    have e1 : MvPowerSeries.subst (fun _ : Unit => (φ : MvPowerSeries Unit ℂ_[p])) M' = PowerSeries.subst M φ := by
      have hS' : MvPowerSeries.HasSubst (fun _ : Unit => (φ : MvPowerSeries Unit ℂ_[p])) :=
        MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hφ0)
      rw [hM', hM, hmul Unit (Xv ()) hX0 τ, hXs]
      unfold G1.mulBy
      rw [msubst_pt (fun _ : Unit => (φ : MvPowerSeries Unit ℂ_[p])) (fun _ => hφ0) g' hOk'
        (by rw [map_mul, lg_cc g' hOk' hX0, mul_zero])]
      refine congrArg g'.pt ?_
      rw [← MvPowerSeries.coe_substAlgHom hS', map_mul, MvPowerSeries.coe_substAlgHom hS', MvPowerSeries.subst_C,
        msubst_lg (fun _ : Unit => (φ : MvPowerSeries Unit ℂ_[p])) (fun _ => hφ0) g' hOk' hX0,
        MvPowerSeries.subst_X hS']
    rw [e1]
    show PowerSeries.subst (PowerSeries.subst M φ) g'.ph = PowerSeries.subst M g.ph + PowerSeries.subst M h
    rw [← PowerSeries.subst_comp_subst_apply (hs1 hφ0) (hs0 hM0), hph, PowerSeries.subst_add (hs0 hM0)]
  have hsR : MvPowerSeries.subst (fun _ : Unit => (φ : MvPowerSeries Unit ℂ_[p]))
      (MvPowerSeries.C ((N : ℤ) : ℂ_[p]) * g'.phAt (Xv ())) =
      MvPowerSeries.C ((N : ℤ) : ℂ_[p]) * g.phAt (Xv ()) + MvPowerSeries.C ((N : ℤ) : ℂ_[p]) * h := by
    have hS' : MvPowerSeries.HasSubst (fun _ : Unit => (φ : MvPowerSeries Unit ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hφ0)
    rw [← MvPowerSeries.coe_substAlgHom hS', map_mul, MvPowerSeries.coe_substAlgHom hS', MvPowerSeries.subst_C,
      msubst_phAt (fun _ : Unit => (φ : MvPowerSeries Unit ℂ_[p])) (fun _ => hφ0) g' hOk' hX0,
      MvPowerSeries.subst_X hS']
    show MvPowerSeries.C ((N : ℤ) : ℂ_[p]) * PowerSeries.subst φ g'.ph = _
    rw [hph]
    unfold G1.phAt
    rw [hXs]
    ring
  rw [hsM', hsR] at hS
  have hHM : Simeq (PowerSeries.subst M h) 0 := S_small hM0 hMI hh0 hhI
  have hH : Simeq (h : MvPowerSeries Unit ℂ_[p]) 0 := ⟨by rw [sub_zero]; exact hh0, by rw [sub_zero]; exact hhI⟩
  have hsmall : Simeq (MvPowerSeries.C ((N : ℤ) : ℂ_[p]) * h + -PowerSeries.subst M h) 0 :=
    simeq_zero_add (S_int hH N) (simeq_zero_neg hHM)
  have B := S_add hS (S_refl (-PowerSeries.subst M h))
  have D2 := S_add (S_refl (MvPowerSeries.C ((N : ℤ) : ℂ_[p]) * g.phAt (Xv ()))) hsmall
  refine S_trans (S_of_eq ?_) (S_trans B (S_trans (S_of_eq ?_) (S_trans D2 (S_of_eq ?_))))
  · ring
  · ring
  · ring

theorem S_shift {σ : Type} {x y J K : MvPowerSeries σ ℂ_[p]} (h : Simeq (x + J) (y + K)) (hJ : Simeq J 0)
    (hK : Simeq K 0) : Simeq x y := by
  have a := S_add h (S_refl (-J))
  have b : Simeq (K + -J) 0 := simeq_zero_add hK (simeq_zero_neg hJ)
  have c := S_add (S_refl y) b
  exact S_trans (S_of_eq (by ring)) (S_trans a (S_trans (S_of_eq (by ring)) (S_trans c (S_of_eq (by ring)))))

theorem biaddInertAll_of (hB : BiaddInert) (hG : GenusOneWittExists) : BiaddInertAll := by
  intro D p _ cc δ g hA h5 hIn
  have hA0 := hA
  obtain ⟨hcurve, hcop, hδ, hLam, hOk⟩ := hA
  obtain ⟨g', hl, hA', hW'⟩ := hG D cc δ hcurve hδ p hcop h5 hIn g.lam
  have hOk' : g'.Ok := hA'.2.2.2.2
  have hL : g'.abelian₂ = g.abelian₂ := hA'.2.2.2.1.trans hLam.symm
  obtain ⟨φ, hφ0, hφI, -, hadd, h, hh0, hhI, hph⟩ := change h5 g g' hOk hOk' hl hL
    (Formalism.MainNotions.Ext.CutA.ePhiOne_holds D p cc δ g hA0) (Formalism.MainNotions.Ext.CutA.ePhiOne_holds D p cc δ g' hA')
  obtain ⟨hB1, hB2⟩ := hB D p cc δ g' hA' h5 hIn hW'
  have hX0 : ∀ i : Fin 3, MvPowerSeries.constantCoeff (Xv i : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  set s : Fin 3 → MvPowerSeries (Fin 3) ℂ_[p] := fun i => PowerSeries.subst (Xv i : MvPowerSeries (Fin 3) ℂ_[p]) φ
    with hs_def
  have hsc : ∀ i, MvPowerSeries.constantCoeff (s i) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (hX0 i) _ hφ0
  have hsI : ∀ i, IntegralMv (s i) := fun i => integral_psubst (hX0 i) (integral_Xv i) hφI
  have hS : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hsc
  have hsX : ∀ i, MvPowerSeries.subst s (Xv i : MvPowerSeries (Fin 3) ℂ_[p]) = PowerSeries.subst (Xv i : MvPowerSeries (Fin 3) ℂ_[p]) φ :=
    fun i => MvPowerSeries.subst_X hS i
  have hphA : ∀ A : MvPowerSeries (Fin 3) ℂ_[p], MvPowerSeries.constantCoeff A = 0 →
      g'.phAt (PowerSeries.subst A φ) = g.phAt A + PowerSeries.subst A h := by
    intro A hA1
    show PowerSeries.subst (PowerSeries.subst A φ) g'.ph = PowerSeries.subst A g.ph + PowerSeries.subst A h
    rw [← PowerSeries.subst_comp_subst_apply (hs1 hφ0) (hs0 hA1), hph, PowerSeries.subst_add (hs0 hA1)]
  have hbe : ∀ a b : MvPowerSeries (Fin 3) ℂ_[p], MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      g'.be (PowerSeries.subst a φ) (PowerSeries.subst b φ) = g.be a b +
        (PowerSeries.subst (g.add a b) h - PowerSeries.subst a h - PowerSeries.subst b h) := by
    intro a b ha hb
    unfold G1.be
    rw [← hadd (Fin 3) a b ha hb, hphA _ (add_cc g hOk ha hb), hphA a ha, hphA b hb]
    ring
  have hH : ∀ y : MvPowerSeries (Fin 3) ℂ_[p], MvPowerSeries.constantCoeff y = 0 → IntegralMv y →
      Simeq (PowerSeries.subst y h) 0 := fun y hy hyI => S_small hy hyI hh0 hhI
  have hJ : ∀ a b : MvPowerSeries (Fin 3) ℂ_[p], MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      IntegralMv a → IntegralMv b →
      Simeq (PowerSeries.subst (g.add a b) h - PowerSeries.subst a h - PowerSeries.subst b h) 0 := by
    intro a b ha hb haI hbI
    have e : PowerSeries.subst (g.add a b) h - PowerSeries.subst a h - PowerSeries.subst b h =
        PowerSeries.subst (g.add a b) h + (-PowerSeries.subst a h + -PowerSeries.subst b h) := by ring
    rw [e]
    exact simeq_zero_add (hH _ (add_cc g hOk ha hb) (integral_add g hA0 ha hb haI hbI))
      (simeq_zero_add (simeq_zero_neg (hH a ha haI)) (simeq_zero_neg (hH b hb hbI)))
  have hI : ∀ i : Fin 3, IntegralMv (Xv i : MvPowerSeries (Fin 3) ℂ_[p]) := fun i => integral_Xv i
  have a01c := add_cc g hOk (hX0 0) (hX0 1)
  have a12c := add_cc g hOk (hX0 1) (hX0 2)
  have a01I := integral_add g hA0 (hX0 0) (hX0 1) (hI 0) (hI 1)
  have a12I := integral_add g hA0 (hX0 1) (hX0 2) (hI 1) (hI 2)
  constructor
  · have T := S_subst s hsc hsI hB1
    rw [msubst_be s hsc g' hOk' (add_cc g' hOk' (hX0 0) (hX0 1)) (hX0 2), msubst_add s hsc g' hOk' (hX0 0) (hX0 1),
      hsX, hsX, hsX, ← hadd (Fin 3) (Xv 0) (Xv 1) (hX0 0) (hX0 1), hbe _ _ a01c (hX0 2)] at T
    rw [← MvPowerSeries.coe_substAlgHom hS, map_add, MvPowerSeries.coe_substAlgHom hS,
      msubst_be s hsc g' hOk' (hX0 0) (hX0 2), msubst_be s hsc g' hOk' (hX0 1) (hX0 2), hsX, hsX, hsX,
      hbe _ _ (hX0 0) (hX0 2), hbe _ _ (hX0 1) (hX0 2)] at T
    have T' := S_trans T (S_of_eq (show g.be (Xv 0) (Xv 2) + (PowerSeries.subst (g.add (Xv 0) (Xv 2)) h -
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) h - PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) h) +
        (g.be (Xv 1) (Xv 2) + (PowerSeries.subst (g.add (Xv 1) (Xv 2)) h -
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) h - PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) h)) =
        (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) + ((PowerSeries.subst (g.add (Xv 0) (Xv 2)) h -
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) h - PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) h) +
        (PowerSeries.subst (g.add (Xv 1) (Xv 2)) h -
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) h - PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) h)) by ring))
    exact S_shift T' (hJ _ _ a01c (hX0 2) a01I (hI 2))
      (simeq_zero_add (hJ _ _ (hX0 0) (hX0 2) (hI 0) (hI 2)) (hJ _ _ (hX0 1) (hX0 2) (hI 1) (hI 2)))
  · have T := S_subst s hsc hsI hB2
    rw [msubst_be s hsc g' hOk' (hX0 0) (add_cc g' hOk' (hX0 1) (hX0 2)), msubst_add s hsc g' hOk' (hX0 1) (hX0 2),
      hsX, hsX, hsX, ← hadd (Fin 3) (Xv 1) (Xv 2) (hX0 1) (hX0 2), hbe _ _ (hX0 0) a12c] at T
    rw [← MvPowerSeries.coe_substAlgHom hS, map_add, MvPowerSeries.coe_substAlgHom hS,
      msubst_be s hsc g' hOk' (hX0 0) (hX0 1), msubst_be s hsc g' hOk' (hX0 0) (hX0 2), hsX, hsX, hsX,
      hbe _ _ (hX0 0) (hX0 1), hbe _ _ (hX0 0) (hX0 2)] at T
    have T' := S_trans T (S_of_eq (show g.be (Xv 0) (Xv 1) + (PowerSeries.subst (g.add (Xv 0) (Xv 1)) h -
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) h - PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) h) +
        (g.be (Xv 0) (Xv 2) + (PowerSeries.subst (g.add (Xv 0) (Xv 2)) h -
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) h - PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) h)) =
        (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2)) + ((PowerSeries.subst (g.add (Xv 0) (Xv 1)) h -
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) h - PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) h) +
        (PowerSeries.subst (g.add (Xv 0) (Xv 2)) h -
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) h - PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) h)) by ring))
    exact S_shift T' (hJ _ _ (hX0 0) a12c (hI 0) a12I)
      (simeq_zero_add (hJ _ _ (hX0 0) (hX0 1) (hI 0) (hI 1)) (hJ _ _ (hX0 0) (hX0 2) (hI 0) (hI 2)))

theorem genus_one_witt_exists_of (h : GenusOneModelExists) : GenusOneWittExists := by
  intro D cc δ hcc hδ p _ hcop h5 hIn lam
  obtain ⟨g, hl, hA, hW, -⟩ := h D cc δ hcc hδ p hcop h5 hIn lam
  exact ⟨g, hl, hA, hW⟩

end Assembly

end Formalism.L2.KerInert.ModelP
