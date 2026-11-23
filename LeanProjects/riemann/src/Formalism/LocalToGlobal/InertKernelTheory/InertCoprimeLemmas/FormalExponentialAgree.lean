import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.CyclicPowerClassOfExpEquiv
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSeriesAtVariable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsSubstitution
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.ExpLog
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC

noncomputable section

namespace Formalism.L2.KerInert.Dict

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField

def SimeqAgree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]),
    Formalism.MainNotions.GL3Theta.Simeq f g ↔ Formalism.InvariantFactorPaths.G7.Simeq f g

def LogAgree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]), IsWq W wq →
    flog W wq = Formalism.L2.Th1.A.logSer W

def ExAgree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → g.ex = Formalism.L2.Th1.A.expSer g.W

def AddAgree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]),
    MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
    g.add a b = MvPowerSeries.subst ![a, b] (Formalism.L2.Th1.A.fgl g.W)

def PhAgree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (s2 : ℂ_[p]), g.Ok →
    PowerSeries.rescale (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) (sgSer g.lam g.abelian₂) =
      PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * Formalism.L2.Th1.B.sgW g.W s2 →
    g.ph = Formalism.L2.Th1.B.phW g.W s2

def SigmaCurveInert : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    ∃ s2 : ℂ_[p], s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧
      PowerSeries.rescale (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) (sgSer g.lam g.abelian₂) =
        PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * Formalism.L2.Th1.B.sgW g.W s2

open PowerSeries

section
variable {p : ℕ} [Fact p.Prime]

theorem expMv_eq_mvExp {σ : Type} {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0) :
    Formalism.MainNotions.TaylorLogMetric.expMv F = Formalism.DworkPowerSeriesWeights.mvExp F :=
  PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.expMv_eq hF

theorem formal_equivalence_agree : SimeqAgree := by
  intro p _ σ f g
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    rw [← expMv_eq_mvExp h0]
    exact h1
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    rw [← expMv_eq_mvExp h0] at h1
    exact h1

theorem dX_eq (f : PowerSeries ℂ_[p]) : dX f = derivative ℂ_[p] f := by
  ext n
  simp [dX, PowerSeries.coeff_derivative, mul_comm]

theorem isWq_C {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    wq = 1 + C W.a₁ * X * wq + C W.a₂ * X ^ 2 * wq + C W.a₃ * X ^ 3 * wq ^ 2 +
      C W.a₄ * X ^ 4 * wq ^ 2 + C W.a₆ * X ^ 6 * wq ^ 3 := by
  exact h

theorem wSer_of_isWq {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    Formalism.L2.Th1.A.wSer W = X ^ 3 * wq := by
  symm
  apply Formalism.L2.Th1.A.CurveSer.wSer_unique
  refine ⟨by simp, ?_⟩
  linear_combination (X ^ 3 : PowerSeries ℂ_[p]) * isWq_C h

theorem cc_wq {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    constantCoeff wq = 1 := by
  have h1 := congrArg constantCoeff (isWq_C h)
  simpa using h1

theorem omegaW_eq {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    omegaW W wq = Formalism.L2.Th1.A.om W := by
  have hw := wSer_of_isWq h
  have hE := (Formalism.L2.Th1.A.CurveSer.wSer_fixed W).2
  have hd := Formalism.L2.Th1.A.CurveSer.deriv_wSer_mul_fw W
  have hfo := Formalism.L2.Th1.A.CurveSer.fw_mul_om W
  have key : Formalism.L2.Th1.A.fw W * (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) =
      wq * (C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2) := by
    apply mul_left_cancel₀ (pow_ne_zero 3 (X_ne_zero (R := ℂ_[p])))
    have hder : derivative ℂ_[p] (X ^ 3 * wq) = 3 * X ^ 2 * wq + X ^ 3 * derivative ℂ_[p] wq := by
      rw [Derivation.leibniz, Derivation.leibniz_pow, derivative_X]
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    simp only [Formalism.L2.Th1.A.fw, Formalism.L2.Th1.A.fu] at hd ⊢
    rw [hw] at hd hE ⊢
    rw [hder] at hd
    rw [dX_eq]
    linear_combination (-X : PowerSeries ℂ_[p]) * hd + 3 * hE
  have hD : constantCoeff (wq * (C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2)) ≠ 0 := by
    have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
    simp [cc_wq h, h2]
  have e1 : (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) =
      Formalism.L2.Th1.A.om W * (wq * (C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2)) := by
    rw [← key, ← mul_assoc, mul_comm (Formalism.L2.Th1.A.om W), hfo, one_mul]
  unfold omegaW
  simp only [PowerSeries.algebraMap_eq]
  rw [e1, mul_assoc, PowerSeries.mul_inv_cancel _ hD, mul_one]

theorem formal_logarithm_agree : LogAgree := by
  intro p _ W wq h
  unfold flog Formalism.L2.Th1.A.logSer Formalism.L2.Th1.A.integ
  rw [omegaW_eq h]

theorem formal_exponential_agree : ExAgree := by
  intro p _ g hOk
  have hl : flog g.W g.wq = Formalism.L2.Th1.A.logSer g.W := formal_logarithm_agree p g.W g.wq hOk.2.1
  obtain ⟨h0, h1, -, -⟩ := Formalism.L2.Th1.A.logSpec ℂ_[p] g.W
  have hu : IsUnit (coeff 1 (Formalism.L2.Th1.A.logSer g.W)) := by rw [h1]; exact isUnit_one
  have hs := Formalism.L2.Th1.A.compInvSpec ℂ_[p] _ h0 hu
  unfold Formalism.L2.Th1.A.expSer
  apply hs.2.2.2.2.1 g.ex hOk.2.2.1
  rw [← hl]
  exact hOk.2.2.2

theorem intModel_of_ok {g : G1 p} (hOk : g.Ok) : Formalism.L2.Th1.A.IntModel g.W := by
  obtain ⟨⟨h1, h2, h3, h4, h6, -⟩, -⟩ := hOk
  exact ⟨h1, h2, h3, h4, h6⟩

theorem formal_addition_agree : AddAgree := by
  intro p _ g hOk σ a b ha hb
  have hl : flog g.W g.wq = Formalism.L2.Th1.A.logSer g.W := formal_logarithm_agree p g.W g.wq hOk.2.1
  have he : g.ex = Formalism.L2.Th1.A.expSer g.W := formal_exponential_agree p g hOk
  have hL := (Formalism.L2.Th1.A.bridgeLaw ℂ_[p] g.W (intModel_of_ok hOk)).1
  have hF : MvPowerSeries.constantCoeff (Formalism.L2.Th1.A.fgl g.W) = 0 := hL.1
  have hc := Formalism.L2.Th1.B.law_constantCoeff_subst2 (Formalism.L2.Th1.A.fgl g.W) hF a b ha hb
  have hsum := Formalism.L2.Th1.B.law_subst hL a b ha hb
  obtain ⟨hl0, -, -, -⟩ := Formalism.L2.Th1.A.logSpec ℂ_[p] g.W
  obtain ⟨-, -, -, hEL, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] g.W
  show PowerSeries.subst (PowerSeries.subst a (flog g.W g.wq) + PowerSeries.subst b (flog g.W g.wq)) g.ex = _
  rw [hl, he, ← hsum, ← PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hl0)
    (HasSubst.of_constantCoeff_zero hc), hEL, PowerSeries.subst_X (HasSubst.of_constantCoeff_zero hc)]

theorem ePhi1_eq (g : G1 p) (s2 : ℂ_[p]) (hOk : g.Ok)
    (hR : PowerSeries.rescale (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) (sgSer g.lam g.abelian₂) =
      PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * Formalism.L2.Th1.B.sgW g.W s2) :
    ePhi1 g.lam g.abelian₂ g.C g.wq = Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.B.phW g.W s2)) := by
  have hl : flog (g.C • wModel g.lam g.abelian₂) g.wq = Formalism.L2.Th1.A.logSer g.W := formal_logarithm_agree p _ g.wq hOk.2.1
  obtain ⟨hl0, -, -, -⟩ := Formalism.L2.Th1.A.logSpec ℂ_[p] g.W
  have hL : HasSubst (Formalism.L2.Th1.A.logSer g.W) := HasSubst.of_constantCoeff_zero' hl0
  have hS := (Formalism.L2.Th1.B.curveSigma ℂ_[p] g.W s2).2.1
  set ep : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hep
  have hep0 : ep ≠ 0 := Units.ne_zero _
  have hlin : PowerSeries.subst (Formalism.L2.Th1.A.logSer g.W) (ep • (X : PowerSeries ℂ_[p])) =
      C ep * Formalism.L2.Th1.A.logSer g.W := by
    rw [PowerSeries.subst_smul hL, PowerSeries.subst_X hL, smul_eq_C_mul]
  have hsub : PowerSeries.subst (C ep * Formalism.L2.Th1.A.logSer g.W) (sgSer g.lam g.abelian₂) =
      C ep * (X * Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.B.phW g.W s2))) := by
    rw [← hlin, ← PowerSeries.subst_comp_subst_apply (HasSubst.X' (R := ℂ_[p]) |>.smul' ep) hL,
      ← PowerSeries.rescale_eq_subst, hR, PowerSeries.subst_mul hL, PowerSeries.subst_C, hS]
    rfl
  ext n
  simp only [ePhi1, coeff_mk, PowerSeries.algebraMap_eq, hl]
  rw [← hep, hsub, coeff_C_mul, coeff_succ_X_mul]
  field_simp

theorem formal_phase_agree : PhAgree := by
  intro p _ g s2 hOk hR
  have he := ePhi1_eq g s2 hOk hR
  have h0 := (Formalism.L2.Th1.B.curveSigma ℂ_[p] g.W s2).1
  have hn : MvPowerSeries.constantCoeff (-(Formalism.L2.Th1.B.phW g.W s2) : MvPowerSeries Unit ℂ_[p]) = 0 := by
    rw [map_neg, neg_eq_zero]
    exact h0
  have h1 := Formalism.L2.Th1.B.constantCoeff_fExp hn
  show -logMv (ePhi1 g.lam g.abelian₂ g.C g.wq) = _
  rw [he, show logMv (Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.B.phW g.W s2))) =
      PI.FglShared.logS (Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.B.phW g.W s2))) from rfl,
    PI.FglShared.logS_eq_subst h1]
  change -(Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.B.phW g.W s2)))) = _
  rw [Formalism.L2.Th1.B.fLog_fExp hn, neg_neg]

end

end Formalism.L2.KerInert.Dict
