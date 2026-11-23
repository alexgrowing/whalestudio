import Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GenusOneWittExistsOf
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LinearCoeffLogShiftedWeierstrass
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne

noncomputable section

namespace Formalism.L2.KerInert.MModel

open PowerSeries
open Formalism.L2.Th1.A (shortW logSer expSer wpReg)
open Formalism.L2.KerInert.MC (phi)

variable {p : ℕ} [Fact p.Prime]

def scaleVC (e : ℂ_[p]ˣ) : WeierstrassCurve.VariableChange ℂ_[p] := ⟨e⁻¹, 0, 0, 0⟩

theorem scaleVC_smul (e : ℂ_[p]ˣ) (g2 g3 : ℂ_[p]) :
    scaleVC e • shortW g2 g3 = shortW ((e : ℂ_[p]) ^ 4 * g2) ((e : ℂ_[p]) ^ 6 * g3) := by
  ext <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, scaleVC, shortW, inv_inv] <;> ring

theorem norm_four (h5 : 5 ≤ p) : ‖(4 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  rw [show (4 : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((4 : ℕ) : ℚ_[p]) by rw [map_natCast]; norm_num,
    norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
  have := Nat.le_of_dvd (by norm_num) hd
  omega

theorem coeffIn_short (h5 : 5 ≤ p) {g2 g3 : ℂ_[p]} (n2 : ‖g2‖ ≤ 1) (n3 : ‖g3‖ ≤ 1) :
    Formalism.L2.Th1.C.CoeffIn (Formalism.L2.KerInert.ModelP.RB p) (shortW g2 g3) := by
  have h4 := norm_four h5
  simp only [Formalism.L2.Th1.C.CoeffIn, Formalism.L2.Th1.C.mem_unitBall_iff, shortW, norm_zero, zero_le_one,
    norm_div, norm_neg, h4, div_one, true_and]
  exact ⟨n2, n3⟩

theorem param (h5 : 5 ≤ p) (g2 g3 ε : ℂ_[p]) (hε : ‖ε‖ = 1) (n2 : ‖g2‖ ≤ 1) (n3 : ‖g3‖ ≤ 1)
    (nd : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (hth : ∀ n, ‖coeff n (Formalism.L2.Th1.D.thetaS p g2 g3 ε)‖ ≤ 1)
    (C : WeierstrassCurve.VariableChange ℂ_[p])
    (i1 : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).a₁‖ ≤ 1) (i2 : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).a₂‖ ≤ 1)
    (i3 : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).a₃‖ ≤ 1) (hΔ : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).Δ‖ = 1) :
    ∃ h : PowerSeries ℂ_[p], constantCoeff h = 0 ∧ (∀ n, ‖coeff n h‖ ≤ 1) ∧ ‖coeff 1 h‖ = 1 ∧
      PowerSeries.C (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * (logSer (C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3))).subst h =
        Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p := by
  have hp2 : 2 ≤ p := by omega
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h, norm_zero] at hε
    exact zero_ne_one hε
  set e : ℂ_[p]ˣ := Units.mk0 ε hε0 with he
  have hee : (e : ℂ_[p]) = ε := rfl
  have hW' : shortW (ε ^ 4 * g2) (ε ^ 6 * g3) = scaleVC e • shortW g2 g3 := by
    rw [scaleVC_smul, hee]
  set D := C * scaleVC e with hD
  have hCD : C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3) = D • shortW g2 g3 := by
    rw [hW', hD, mul_smul]
  have hΔ0 : (shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
    simp only [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have hW0int : Formalism.L2.Th1.C.CoeffIn (Formalism.L2.KerInert.ModelP.RB p) (shortW g2 g3) :=
    coeffIn_short h5 n2 n3
  obtain ⟨hu, hui, hr, hs, ht⟩ := Formalism.L2.KerInert.ModelP.vc_gen h5 (shortW g2 g3)
    (by simp [shortW]) (by simp [shortW]) (by simp [shortW]) (by rw [hΔ0, nd]) D
    (by rw [← hCD]; exact i1) (by rw [← hCD]; exact i2) (by rw [← hCD]; exact i3)
    (by rw [← hCD]; exact hΔ)
  have hsu : ((scaleVC e).u : ℂ_[p]) = ε⁻¹ := by
    show ((e⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ε⁻¹
    rw [Units.val_inv_eq_inv_val, hee]
  have hDu : (D.u : ℂ_[p]) = C.u * ε⁻¹ := by
    rw [← hsu]
    rfl
  have hCu : ‖(C.u : ℂ_[p])‖ = 1 := by
    rw [hDu, norm_mul, norm_inv, hε, inv_one, mul_one] at hu
    exact hu
  have hphiInt : Formalism.L2.Th1.C.IntPS (Formalism.L2.KerInert.ModelP.RB p) (phi (shortW g2 g3) D) :=
    Formalism.L2.KerInert.MC.intPS_phi (shortW g2 g3) hW0int D
      ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr hu.le) ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr hr)
      ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr hs) ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr ht)
  have hthInt : Formalism.L2.Th1.C.IntPS (Formalism.L2.KerInert.ModelP.RB p) (Formalism.L2.Th1.D.thetaS p g2 g3 ε) :=
    fun n => (Formalism.L2.Th1.C.mem_unitBall_iff _).mpr (hth n)
  have hlg0 : constantCoeff (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) = 0 :=
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_lgF p hp2
  have hth0 : constantCoeff (Formalism.L2.Th1.D.thetaS p g2 g3 ε) = 0 := by
    simp only [Formalism.L2.Th1.D.thetaS]
    refine PowerSeries.constantCoeff_subst_eq_zero
      (by rw [map_mul]; exact mul_eq_zero_of_right _ hlg0) _ ?_
    simp [Formalism.L2.Th1.CM.uSer]
  set b : PowerSeries ℂ_[p] := PowerSeries.C (C.u : ℂ_[p]) * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hbdef
  have hb0 : constantCoeff b = 0 := by simp [hbdef, hlg0]
  have hb : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero' hb0
  obtain ⟨hE0, hE1, hEL, -, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] (D • shortW g2 g3)
  have hE : PowerSeries.HasSubst (expSer (D • shortW g2 g3)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hE0
  have hh : PowerSeries.subst b (expSer (D • shortW g2 g3)) =
      PowerSeries.subst (Formalism.L2.Th1.D.thetaS p g2 g3 ε) (phi (shortW g2 g3) D) := by
    have hCX0 : constantCoeff (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X : PowerSeries ℂ_[p]) = 0 := by
      simp
    have hCX : PowerSeries.HasSubst (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X : PowerSeries ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hCX0
    obtain ⟨hE00, -, -, -, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] (shortW g2 g3)
    have hA : PowerSeries.HasSubst (PowerSeries.subst (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X)
        (expSer (shortW g2 g3))) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (PowerSeries.constantCoeff_subst_eq_zero hCX0 _ hE00)
    rw [Formalism.L2.KerInert.MC.exp_eq, PowerSeries.subst_comp_subst_apply hA hb,
      PowerSeries.subst_comp_subst_apply hCX hb]
    congr 1
    have hsb : PowerSeries.subst b (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X : PowerSeries ℂ_[p]) =
        PowerSeries.C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p := by
      rw [PowerSeries.subst_mul hb, PowerSeries.subst_X hb, PowerSeries.subst_C]
      show PowerSeries.C _ * b = _
      rw [hbdef, ← mul_assoc, ← map_mul, Units.val_inv_eq_inv_val, hDu]
      congr 2
      field_simp
    rw [hsb, Formalism.L2.Th1.D.thetaS, Formalism.L2.Th1.A.uSerEq]
  refine ⟨PowerSeries.subst b (expSer (D • shortW g2 g3)), ?_, ?_, ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hb0 _ hE0
  · intro n
    rw [hh]
    exact (Formalism.L2.Th1.C.mem_unitBall_iff _).mp
      (Formalism.L2.KerInert.MC.intPS_subst' _ hphiInt hthInt hth0 n)
  · rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hb0, hE1, one_mul, hbdef, PowerSeries.coeff_C_mul,
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF p hp2, mul_one, hCu]
  · rw [hCD, ← PowerSeries.subst_comp_subst_apply hE hb, hEL, PowerSeries.subst_X hb, hbdef,
      ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

section Exp

open Formalism.L2.Th1.B (fExp fLog sigS sigma lU fExp_add constantCoeff_fExp fExp_fLog constantCoeff_fLog)

theorem X_mul_shift (f : PowerSeries ℂ_[p]) (hf : constantCoeff f = 0) :
    f = X * PowerSeries.mk (fun n => coeff (n + 1) f) := by
  have h := PowerSeries.sub_const_eq_X_mul_shift f
  rwa [hf, map_zero, sub_zero] at h

theorem subst_fExp {a f : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (hf : constantCoeff f = 0) :
    PowerSeries.subst a (fExp (ι := Unit) f) = fExp (ι := Unit) (PowerSeries.subst a f) := by
  simp only [fExp]
  exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hf)
    (PowerSeries.HasSubst.of_constantCoeff_zero' ha) _

theorem sig_at (h5 : 5 ≤ p) (g2 g3 s2 ε : ℂ_[p]) :
    (Formalism.L2.Th1.B.sgStar s2 (wpReg (shortW g2 g3))).subst (PowerSeries.C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) =
      PowerSeries.C ε * X * fExp (-Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) := by
  have hp2 : 2 ≤ p := by omega
  set L : PowerSeries ℂ_[p] := PowerSeries.C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hLdef
  set P := wpReg (shortW g2 g3)
  have hlg0 : constantCoeff (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) = 0 :=
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_lgF p hp2
  have hL0 : constantCoeff L = 0 := by simp [hLdef, hlg0]
  have hL : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero' hL0
  have hS0 : constantCoeff (sigS P) = 0 := by
    simp [sigS, Formalism.L2.Th1.B.constantCoeff_prim]
  have hQ0 : constantCoeff (-(PowerSeries.C (s2 / 2) * X ^ 2 : PowerSeries ℂ_[p])) = 0 := by simp
  have hA0 : constantCoeff (PowerSeries.subst L (sigS P)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hL0 _ hS0
  have hB0 : constantCoeff (-(PowerSeries.C (s2 / 2) * L ^ 2)) = 0 := by simp [hL0]
  have hAB : constantCoeff (PowerSeries.subst L (sigS P) + -(PowerSeries.C (s2 / 2) * L ^ 2)) = 0 := by
    rw [map_add, hA0, hB0, add_zero]
  have hU1 : constantCoeff (lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p)) = 1 := by
    have h := Formalism.InvariantFactorPaths.G7.coeff_lgF_pow ℂ_[p] hp2 0
    simp only [pow_zero, inv_one] at h
    simpa [lU] using h
  have hF0 : constantCoeff (fLog (lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p))) = 0 :=
    constantCoeff_fLog hU1
  have hXU : X * lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) = Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p :=
    (X_mul_shift _ hlg0).symm
  have hL' : L = PowerSeries.C ε * X * lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) := by
    rw [mul_assoc, hXU]
  have hsubQ : PowerSeries.subst L (-(PowerSeries.C (s2 / 2) * X ^ 2 : PowerSeries ℂ_[p])) =
      -(PowerSeries.C (s2 / 2) * L ^ 2) := by
    rw [← PowerSeries.coe_substAlgHom hL, map_neg, map_mul, map_pow, PowerSeries.coe_substAlgHom hL,
      PowerSeries.subst_X hL, PowerSeries.subst_C]
    rfl
  have hphi : -Formalism.L2.Th1.D.phFF p g2 g3 s2 ε =
      PowerSeries.subst L (sigS P) + -(PowerSeries.C (s2 / 2) * L ^ 2) +
        fLog (lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p)) := by
    simp only [Formalism.L2.Th1.D.phFF]
    ring
  rw [hphi, fExp_add hAB hF0, fExp_add hA0 hB0, fExp_fLog hU1]
  simp only [Formalism.L2.Th1.B.sgStar, sigma]
  rw [PowerSeries.subst_mul hL, PowerSeries.subst_mul hL, PowerSeries.subst_X hL,
    subst_fExp hL0 hS0, subst_fExp hL0 hQ0, hsubQ]
  generalize fExp (PowerSeries.subst L (sigS P)) = a
  generalize fExp (-(PowerSeries.C (s2 / 2) * L ^ 2)) = b
  rw [hL']
  ring

end Exp

section EPart

open Formalism.L2.Th1.B (fExp fExp_add constantCoeff_fExp)

end EPart

section Comparison₂

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

end Comparison₂

end Formalism.L2.KerInert.MModel
