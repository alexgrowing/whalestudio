import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMRead
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeW
import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.FinalOfNRDense
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.HomotheticLatticeIntegralOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementL
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly

noncomputable section

namespace GlobalTheory.CurveDictionary

open Formalism.L2.G.Pend (k0ToC)
open Formalism.InvariantFactorPaths.G7 (lgF)

theorem lgF_eq_logF (l : ℕ) [Fact l.Prime] :
    PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) = lgF ℂ_[l] l := by
  rw [Formalism.L2.G.Pend.logF_map (p := l)]
  ext n
  unfold Formalism.MainNotions.GL3Theta.logF lgF
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul]

theorem cc_lgF' (K : Type) [Field K] (l : ℕ) : PowerSeries.constantCoeff (lgF K l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [lgF]

end GlobalTheory.CurveDictionary

noncomputable section

namespace GlobalTheory.CurveDictionary

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.KerInert.ParameterChangeLemmas Formalism.L2.KerInert.IntegralOrthonormalChange

variable {p : ℕ} [Fact p.Prime]

def scC (ν : ℂ_[p]) (hν : ν ≠ 0) : WeierstrassCurve.VariableChange ℂ_[p] := ⟨Units.mk0 ν hν, 0, 0, 0⟩

section Scale

variable (ν : ℂ_[p]) (hν : ν ≠ 0)

theorem scC_uinv : (((scC ν hν).u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ν⁻¹ := by simp [scC]

theorem scale_weierstrass_a1 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₁ = ν⁻¹ * W.a₁ := by
  rw [WeierstrassCurve.variableChange_a₁, scC_uinv]; simp [scC]

theorem scale_weierstrass_a2 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₂ = ν⁻¹ ^ 2 * W.a₂ := by
  rw [WeierstrassCurve.variableChange_a₂, scC_uinv]; simp [scC]

theorem scale_weierstrass_a3 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₃ = ν⁻¹ ^ 3 * W.a₃ := by
  rw [WeierstrassCurve.variableChange_a₃, scC_uinv]; simp [scC]

theorem scale_weierstrass_a4 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₄ = ν⁻¹ ^ 4 * W.a₄ := by
  rw [WeierstrassCurve.variableChange_a₄, scC_uinv]; simp [scC]

theorem scale_weierstrass_a6 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₆ = ν⁻¹ ^ 6 * W.a₆ := by
  rw [WeierstrassCurve.variableChange_a₆, scC_uinv]; simp [scC]

theorem rescale_C' (c a : ℂ_[p]) : PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with hn
  · rw [hn, pow_zero, one_mul]
  · rw [mul_zero]

theorem rescale_alg (c a : ℂ_[p]) :
    PowerSeries.rescale c (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a) = algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a := by
  rw [PowerSeries.algebraMap_eq]; exact rescale_C' c a

theorem cc_rescale (c : ℂ_[p]) (f : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (PowerSeries.rescale c f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem rescale_inv (c : ℂ_[p]) (f : PowerSeries ℂ_[p]) :
    PowerSeries.rescale c f⁻¹ = (PowerSeries.rescale c f)⁻¹ := by
  by_cases hf : PowerSeries.constantCoeff f = 0
  · rw [PowerSeries.inv_eq_zero.mpr hf, map_zero, PowerSeries.inv_eq_zero.mpr ((cc_rescale c f).trans hf)]
  · rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [cc_rescale]; exact hf), ← map_mul,
      PowerSeries.inv_mul_cancel _ hf, map_one]

theorem X_dX_rescale (c : ℂ_[p]) (f : PowerSeries ℂ_[p]) :
    PowerSeries.X * dX (PowerSeries.rescale c f) = PowerSeries.rescale c (PowerSeries.X * dX f) := by
  ext n
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
    simp only [dX, PowerSeries.coeff_mk, PowerSeries.coeff_rescale]
    ring

theorem isWq_scale (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (h : IsWq W wq) :
    IsWq (scC ν hν • W) (PowerSeries.rescale ν⁻¹ wq) := by
  unfold IsWq at h ⊢
  dsimp only at h ⊢
  conv_lhs => rw [h]
  rw [scale_weierstrass_a1, scale_weierstrass_a2, scale_weierstrass_a3, scale_weierstrass_a4, scale_weierstrass_a6]
  simp only [map_add, map_mul, map_pow, map_one, PowerSeries.rescale_X, PowerSeries.algebraMap_eq, rescale_C']
  ring

theorem omegaW_scale (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    omegaW (scC ν hν • W) (PowerSeries.rescale ν⁻¹ wq) = PowerSeries.rescale ν⁻¹ (omegaW W wq) := by
  unfold omegaW
  dsimp only
  rw [scale_weierstrass_a1, scale_weierstrass_a3]
  have hnum : (-(2 : PowerSeries ℂ_[p]) * PowerSeries.rescale ν⁻¹ wq - PowerSeries.X * dX (PowerSeries.rescale ν⁻¹ wq)) =
      PowerSeries.rescale ν⁻¹ (-(2 : PowerSeries ℂ_[p]) * wq - PowerSeries.X * dX wq) := by
    rw [X_dX_rescale, map_sub]
    congr 1
    simp only [map_mul, map_neg, map_ofNat]
  have hden : PowerSeries.rescale ν⁻¹ wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (ν⁻¹ * W.a₁) * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (ν⁻¹ ^ 3 * W.a₃) * PowerSeries.X ^ 3 * PowerSeries.rescale ν⁻¹ wq - 2) =
      PowerSeries.rescale ν⁻¹ (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
        algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, PowerSeries.rescale_X,
      PowerSeries.algebraMap_eq, rescale_C']
    ring
  rw [hnum, hden, ← rescale_inv, ← map_mul]

theorem flog_scale (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    flog (scC ν hν • W) (PowerSeries.rescale ν⁻¹ wq) = PowerSeries.C ν * PowerSeries.rescale ν⁻¹ (flog W wq) := by
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
  unfold flog
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, omegaW_scale]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, PowerSeries.coeff_rescale]
    have h1 : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν
    rw [pow_succ]
    linear_combination (-(ν⁻¹ ^ n * PowerSeries.coeff n (omegaW W wq) / ((n + 1 : ℕ) : ℂ_[p]))) * h1

end Scale

section Subst

theorem hasSubst_cX (c : ℂ_[p]) : PowerSeries.HasSubst (c • (PowerSeries.X : PowerSeries ℂ_[p])) :=
  (PowerSeries.HasSubst.X' (R := ℂ_[p])).smul' c

theorem subst_rescale_arg (c : ℂ_[p]) (A f : PowerSeries ℂ_[p]) (hA : PowerSeries.constantCoeff A = 0) :
    PowerSeries.subst (PowerSeries.rescale c A) f = PowerSeries.rescale c (PowerSeries.subst A f) := by
  rw [PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hA) (hasSubst_cX c)]

theorem subst_Cmul_rescale (a : ℂ_[p]) (ha : a ≠ 0) (h f : PowerSeries ℂ_[p])
    (h0 : PowerSeries.constantCoeff h = 0) :
    PowerSeries.subst (PowerSeries.C a * h) (PowerSeries.rescale a⁻¹ f) = PowerSeries.subst h f := by
  have h1 : PowerSeries.constantCoeff (PowerSeries.C a * h) = 0 := by rw [map_mul, h0, mul_zero]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' h1
  rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply (hasSubst_cX a⁻¹) hs]
  congr 1
  rw [PowerSeries.subst_smul hs, PowerSeries.subst_X hs, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ ha, map_one, one_mul]

end Subst

theorem scC_mul_uinv (ν : ℂ_[p]) (hν : ν ≠ 0) (C : WeierstrassCurve.VariableChange ℂ_[p]) :
    (((scC ν hν * C).u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ν⁻¹ * ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) := by
  rw [WeierstrassCurve.VariableChange.mul_def]
  simp [scC, mul_comm]

theorem ePhi1_scale (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (C : WeierstrassCurve.VariableChange ℂ_[p])
    (wq : PowerSeries ℂ_[p]) (ν : ℂ_[p]) (hν : ν ≠ 0) :
    ePhi1 lam Λ (scC ν hν * C) (PowerSeries.rescale ν⁻¹ wq) = PowerSeries.rescale ν⁻¹ (ePhi1 lam Λ C wq) := by
  have hW : (scC ν hν * C) • wModel lam Λ = scC ν hν • (C • wModel lam Λ) := mul_smul _ _ _
  set ep : ℂ_[p] := ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hep
  have hep0 : ep ≠ 0 := Units.ne_zero _
  set fl := flog (C • wModel lam Λ) wq with hfl
  have hA0 : PowerSeries.constantCoeff (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep * fl) = 0 := by
    rw [map_mul, hfl, flog_constantCoeff, mul_zero]
  have harg : algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (ν⁻¹ * ep) * flog (scC ν hν • (C • wModel lam Λ))
      (PowerSeries.rescale ν⁻¹ wq) = PowerSeries.rescale ν⁻¹ (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep * fl) := by
    rw [flog_scale ν hν, map_mul (PowerSeries.rescale ν⁻¹) _ _, rescale_alg, PowerSeries.algebraMap_eq, ← hfl,
      ← mul_assoc, ← map_mul, show ν⁻¹ * ep * ν = ep by field_simp]
  ext n
  unfold ePhi1
  dsimp only
  rw [hW, scC_mul_uinv, ← hep, harg, subst_rescale_arg _ _ _ hA0, PowerSeries.coeff_mk, PowerSeries.coeff_rescale,
    PowerSeries.coeff_rescale, PowerSeries.coeff_mk, mul_inv, inv_inv]
  have h1 : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν
  rw [pow_succ]
  linear_combination (ν⁻¹ ^ n * ep⁻¹ * PowerSeries.coeff (n + 1)
    (PowerSeries.subst (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep * fl) (sgSer lam Λ))) * h1

theorem isModel_scale (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (C : WeierstrassCurve.VariableChange ℂ_[p])
    (hU : Formalism.MainNotions.GL3Theta.IsModelU lam Λ C) (ν : ℂ_[p]) (hν : ν ≠ 0) (hν1 : ‖ν‖ = 1)
    (hν12 : ν ^ 12 = (C • wModel lam Λ).Δ) : IsModel lam Λ (scC ν hν * C) := by
  obtain ⟨h1, h2, h3, h4, h6, -⟩ := hU
  have hW : (scC ν hν * C) • wModel lam Λ = scC ν hν • (C • wModel lam Λ) := mul_smul _ _ _
  have hn : ‖ν⁻¹‖ = 1 := by rw [norm_inv, hν1, inv_one]
  show IsIntP ((scC ν hν * C) • wModel lam Λ).a₁ ∧ IsIntP ((scC ν hν * C) • wModel lam Λ).a₂ ∧
    IsIntP ((scC ν hν * C) • wModel lam Λ).a₃ ∧ IsIntP ((scC ν hν * C) • wModel lam Λ).a₄ ∧
    IsIntP ((scC ν hν * C) • wModel lam Λ).a₆ ∧ ((scC ν hν * C) • wModel lam Λ).Δ = 1
  rw [hW]
  unfold IsIntP at h1 h2 h3 h4 h6 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [scale_weierstrass_a1, norm_mul, hn, one_mul]; exact h1
  · rw [scale_weierstrass_a2, norm_mul, norm_pow, hn, one_pow, one_mul]; exact h2
  · rw [scale_weierstrass_a3, norm_mul, norm_pow, hn, one_pow, one_mul]; exact h3
  · rw [scale_weierstrass_a4, norm_mul, norm_pow, hn, one_pow, one_mul]; exact h4
  · rw [scale_weierstrass_a6, norm_mul, norm_pow, hn, one_pow, one_mul]; exact h6
  · rw [WeierstrassCurve.variableChange_Δ, scC_uinv, ← hν12, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hν)]

theorem dict_core (hp2 : p ≠ 2) (D : D7) {N N' r : ℕ} (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (h : PowerSeries ℂ_[p]) (h0 : PowerSeries.constantCoeff h = 0) (hI : ∀ n, IsIntP (PowerSeries.coeff n h))
    (κ : ℂ_[p])
    (hlog : PowerSeries.subst h (flog (C • wModel lam Λ) wq) =
      PowerSeries.C κ * PowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (Formalism.MainNotions.FormalGroupSystem.logF p))
    (ph V : PowerSeries ℂ_[p]) (hph0 : PowerSeries.constantCoeff ph = 0) (hV : ∀ n, IsIntP (PowerSeries.coeff n V))
    (hexp : (Formalism.L2.Th1.C.mvExp ph : PowerSeries ℂ_[p]) = V * (PowerSeries.subst h (ePhi1 lam Λ C wq))⁻¹)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])
    (hInt : IntegralMv (atLog D lam Λ C wq b G * ePh lam Λ C wq r)) :
    Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries (Fin r) ℂ_[p]) *
      @Formalism.MainNotions.FormalGroupSystem.inParamK p _ (Fin r) ℂ_[p] _ (Formalism.L2.G.Pend.wittFractionAlgebraCp p)
        (Formalism.L2.KerInert.Rep.thOrth D lam (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * κ) b G)) := by
  set S : Fin r → MvPowerSeries (Fin r) ℂ_[p] :=
    fun i => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) h with hS
  have hS0 : ∀ i, MvPowerSeries.constantCoeff (S i) = 0 := fun i => constantCoeff_inVar_eq_zero i h h0
  have hSs : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero hS0
  have hSI : ∀ i, IntegralMv (S i) := fun i => integral_subst_single_variable i h hI
  have hh : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hl0 := flog_constantCoeff (C • wModel lam Λ) wq
  set L : PowerSeries ℂ_[p] := PowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (Formalism.MainNotions.FormalGroupSystem.logF p) with hL
  have hL0 : PowerSeries.constantCoeff L = 0 := by
    rw [hL, GlobalTheory.CurveDictionary.lgF_eq_logF]; exact GlobalTheory.CurveDictionary.cc_lgF' _ _
  have hCalg : ∀ x : ℂ_[p], (MvPowerSeries.C x : MvPowerSeries (Fin r) ℂ_[p]) =
      algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) x := fun x => by rw [MvPowerSeries.algebraMap_apply]; rfl

  have hA : MvPowerSeries.subst S (atLog D lam Λ C wq b G) =
      @Formalism.MainNotions.FormalGroupSystem.inParamK p _ (Fin r) ℂ_[p] _ (Formalism.L2.G.Pend.wittFractionAlgebraCp p)
        (Formalism.L2.KerInert.Rep.thOrth D lam (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * κ) b G) := by
    have hXfl : ∀ i : Fin r, MvPowerSeries.constantCoeff (PowerSeries.subst
        (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) = 0 :=
      fun i => constantCoeff_inVar_eq_zero i _ hl0
    have hΦ : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
        ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
          (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
          PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      simp [map_sum, hXfl]
    have hT : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
        ∑ i, MvPowerSeries.C ((((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * κ) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
          (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      simp [map_sum]
    have hP : MvPowerSeries.HasSubst (fun i : Fin r => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) L) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => constantCoeff_inVar_eq_zero i L hL0)
    unfold atLog Formalism.L2.KerInert.Rep.thOrth Formalism.MainNotions.FormalGroupSystem.inParamK
    dsimp only
    rw [MvPowerSeries.subst_comp_subst_apply hΦ hSs]
    erw [MvPowerSeries.subst_comp_subst_apply hT hP]
    congr 1
    funext k
    rw [← MvPowerSeries.coe_substAlgHom hSs, map_sum]
    erw [← MvPowerSeries.coe_substAlgHom hP, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hCalg]
    simp only [map_mul, AlgHom.commutes, MvPowerSeries.coe_substAlgHom, subst_single_var S hSs, MvPowerSeries.subst_X hP]
    rw [hS]
    dsimp only
    rw [← PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X i), hlog,
      PowerSeries.subst_mul (PowerSeries.HasSubst.X i), PowerSeries.subst_C]
    have hid : ∀ x : ℂ_[p], algebraMap ℂ_[p] ℂ_[p] x = x := fun _ => rfl
    simp only [MvPowerSeries.algebraMap_apply, hid]
    rw [hL]
    ring

  have hB : MvPowerSeries.subst S (ePh lam Λ C wq r) =
      ∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])
        (PowerSeries.subst h (ePhi1 lam Λ C wq))⁻¹ := by
    unfold ePh
    rw [if_neg hp2, ← MvPowerSeries.coe_substAlgHom hSs, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coe_substAlgHom, ← subst_inv _ (MvPowerSeries.constantCoeff_X i), subst_single_var S hSs, hS]
    dsimp only
    rw [← subst_inv h h0, PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X i)]

  have hE : Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries (Fin r) ℂ_[p]) =
      (∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) V) *
        MvPowerSeries.subst S (ePh lam Λ C wq r) := by
    rw [hB, ← Finset.prod_mul_distrib]
    change Formalism.L2.Th1.C.mvExp (∑ i, Formalism.InvariantFactorPaths.G7.at1 i ph) = _
    simp only [Formalism.InvariantFactorPaths.G7.at1]
    rw [Formalism.L2.Th1.C.mvExp_sum _ _ (fun i _ => constantCoeff_inVar_eq_zero i ph hph0)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Formalism.L2.Th1.C.subst_mvExp hph0 (MvPowerSeries.constantCoeff_X i), hexp,
      PowerSeries.subst_mul (PowerSeries.HasSubst.X i)]

  have hSG := integral_subst S hS0 hSI hInt
  rw [← MvPowerSeries.coe_substAlgHom hSs, map_mul, MvPowerSeries.coe_substAlgHom, hA] at hSG
  have hU : IntegralMv (∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) V) :=
    integral_prod _ _ fun i _ => integral_subst_single_variable i V hV
  have key := integral_mul hU hSG
  rw [hE]
  have e : (∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) V) *
      MvPowerSeries.subst S (ePh lam Λ C wq r) *
      @Formalism.MainNotions.FormalGroupSystem.inParamK p _ (Fin r) ℂ_[p] _ (Formalism.L2.G.Pend.wittFractionAlgebraCp p)
        (Formalism.L2.KerInert.Rep.thOrth D lam (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * κ) b G) =
      (∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) V) *
      (@Formalism.MainNotions.FormalGroupSystem.inParamK p _ (Fin r) ℂ_[p] _ (Formalism.L2.G.Pend.wittFractionAlgebraCp p)
        (Formalism.L2.KerInert.Rep.thOrth D lam (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * κ) b G) *
        MvPowerSeries.subst S (ePh lam Λ C wq r)) := by ring
  rw [e]
  exact key

end GlobalTheory.CurveDictionary

namespace GlobalTheory.CurveDictionary

open NumberField Formalism.BasicNotions

theorem sgStar_lattice (L : PeriodPair) :
    Formalism.MainNotions.TaylorLogMetric.sgStar L.lattice.toAddSubgroup = Formalism.L2.Th1.F.sgStar L := by
  rw [GlobalTheory.OddTheta.sgStar_eq L L.lattice.toAddSubgroup (fun _ => Iff.rfl), GlobalTheory.Mem.Col2.ThetaVec.sgStar_eq]

theorem taylor_sgStar_map (L : PeriodPair) (a2 a3 s0 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : L.g₂ = a2) (h3 : L.g₃ = a3)
    (hs : Formalism.L2.Th1.F.s2 L = s0) :
    Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.sgStar L) =
      PowerSeries.map (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) (Formalism.L2.Th1.B.sgStar s0 (Formalism.L2.Th1.F.pOf a2 a3)) := by
  rw [Formalism.L2.Th1.F.taylorSgStar L, Formalism.L2.Th1.F.pOfLattice L, h2, h3, hs]
  have hm := Formalism.L2.Th1.F.seriesMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) a2 a3 s0
    (Formalism.L2.Th1.F.pOf a2 a3)
  rw [hm.2.2.2.2.2, hm.2.2.1]
  rfl

theorem sgSer_eq {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (L : PeriodPair)
    (a2 a3 s0 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : L.g₂ = a2) (h3 : L.g₃ = a3) (hs : Formalism.L2.Th1.F.s2 L = s0) :
    Formalism.MainNotions.TaylorLogMetric.sgSer lam L.lattice.toAddSubgroup =
      Formalism.L2.Th1.B.sgStar (lam s0) (Formalism.L2.Th1.F.pOf (lam a2) (lam a3)) := by
  have hT := taylor_sgStar_map L a2 a3 s0 h2 h3 hs
  have e : Formalism.MainNotions.TaylorLogMetric.sgSer lam L.lattice.toAddSubgroup =
      PowerSeries.map lam (Formalism.L2.Th1.B.sgStar s0 (Formalism.L2.Th1.F.pOf a2 a3)) := by
    ext n
    have hn := congrArg (PowerSeries.coeff n) hT
    unfold Formalism.L2.Th1.F.taylor0 at hn
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_map] at hn
    unfold Formalism.MainNotions.TaylorLogMetric.sgSer
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_map, sgStar_lattice L, hn]
    exact GlobalTheory.InertGenusOne.lamC_coe lam _
  have hm := Formalism.L2.Th1.F.seriesMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ_[p] lam a2 a3 s0 (Formalism.L2.Th1.F.pOf a2 a3)
  rw [e, hm.2.2.2.2.2, hm.2.2.1]

theorem wModel_g {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (a2 a3 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : Formalism.MainNotions.TaylorLogMetric.g2 Λ = a2) (h3 : Formalism.MainNotions.TaylorLogMetric.g3 Λ = a3) :
    Formalism.L2.Th1.A.g₂ (Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) = lam a2 ∧ Formalism.L2.Th1.A.g₃ (Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) = lam a3 := by
  have e4 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 Λ) / 4) = -(lam a2) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g2 Λ) / 4 = ((-a2 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by rw [h2]; push_cast; rfl
    rw [this, GlobalTheory.InertGenusOne.lamC_coe, map_div₀, map_neg, map_ofNat]
  have e6 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 Λ) / 4) = -(lam a3) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g3 Λ) / 4 = ((-a3 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by rw [h3]; push_cast; rfl
    rw [this, GlobalTheory.InertGenusOne.lamC_coe, map_div₀, map_neg, map_ofNat]
  simp only [Formalism.L2.Th1.A.g₂, Formalism.L2.Th1.A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, Formalism.MainNotions.TaylorLogMetric.wModel, e4, e6]
  constructor <;> ring

theorem g_change {p : ℕ} [Fact p.Prime] (C : WeierstrassCurve.VariableChange ℂ_[p]) (W : WeierstrassCurve ℂ_[p]) :
    Formalism.L2.Th1.A.g₂ (C • W) = ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 4 * Formalism.L2.Th1.A.g₂ W ∧
      Formalism.L2.Th1.A.g₃ (C • W) = ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 * Formalism.L2.Th1.A.g₃ W := by
  simp only [Formalism.L2.Th1.A.g₂, Formalism.L2.Th1.A.g₃, WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_c₆]
  constructor <;> ring

theorem wpReg_eq {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) :
    Formalism.L2.Th1.A.wpReg W = Formalism.L2.Th1.F.pOf (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W) :=
  Formalism.L2.Th1.F.isWpUnique K _ _ _ _ (Formalism.L2.Th1.A.bridgeWp K W) (Formalism.L2.Th1.F.pOfIsWp K _ _)

section Int

variable {p : ℕ} [Fact p.Prime]

theorem wp_sub_kur (x : ℂ_[p]) (hx : x ∈ Formalism.MainNotions.GL3Theta.Wp p) : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p := by
  have hp : p.Prime := Fact.out
  have hle : Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} ≤
      (Subfield.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ ζ ^ n = 1}).toSubring := by
    rw [Subring.closure_le]
    rintro ζ ⟨n, hn, hc, hz⟩
    exact Subfield.subset_closure ⟨n, hn, (Nat.Prime.coprime_iff_not_dvd hp).1 hc.symm, hz⟩
  have hsub : ((Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} : Subring ℂ_[p]) :
      Set ℂ_[p]) ⊆ ((Subfield.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ ζ ^ n = 1} : Subfield ℂ_[p]) :
      Set ℂ_[p]) := fun y hy => hle hy
  exact closure_mono hsub hx

theorem nadd {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem nmul {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem nsub {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]; exact nadd hx (by rwa [norm_neg])

theorem nnat (n : ℕ) : ‖(n : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℂ_[p] n

theorem nofNat (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : ℂ_[p])‖ ≤ 1 := by
  have := nnat (p := p) (OfNat.ofNat n); rwa [Nat.cast_ofNat] at this

theorem not_dvd_23 (hp : p.Prime) (h5 : 5 ≤ p) (a b : ℕ) : ¬ p ∣ 2 ^ a * 3 ^ b := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega

theorem padic_norm_twelve_eq_one_of_five_le (h5 : 5 ≤ p) : ‖(12 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p)
    (not_dvd_23 hp h5 2 1)
  norm_num at this
  exact this

theorem padicNorm_twoHundredSixteen_eq_one_of_five_le (h5 : 5 ≤ p) : ‖(216 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p)
    (not_dvd_23 hp h5 3 3)
  norm_num at this
  exact this

theorem inv_good (W : WeierstrassCurve ℂ_[p]) (h5 : 5 ≤ p) (i1 : ‖W.a₁‖ ≤ 1) (i2 : ‖W.a₂‖ ≤ 1)
    (i3 : ‖W.a₃‖ ≤ 1) (i4 : ‖W.a₄‖ ≤ 1) (i6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1)
    (w1 : W.a₁ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w2 : W.a₂ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w3 : W.a₃ ∈ Formalism.MainNotions.GL3Theta.Wp p)
    (w4 : W.a₄ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w6 : W.a₆ ∈ Formalism.MainNotions.GL3Theta.Wp p) :
    Formalism.L2.Th1.A.g₂ W ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ Formalism.L2.Th1.A.g₃ W ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧
      ‖Formalism.L2.Th1.A.g₂ W‖ ≤ 1 ∧ ‖Formalism.L2.Th1.A.g₃ W‖ ≤ 1 ∧
      ‖Formalism.L2.Th1.A.g₂ W ^ 3 - 27 * Formalism.L2.Th1.A.g₃ W ^ 2‖ = 1 := by
  have k1 := wp_sub_kur _ w1
  have k2 := wp_sub_kur _ w2
  have k3 := wp_sub_kur _ w3
  have k4 := wp_sub_kur _ w4
  have k6 := wp_sub_kur _ w6
  have hb2 : W.b₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.b₂‖ ≤ 1 := by
    unfold WeierstrassCurve.b₂
    exact ⟨add_mem (pow_mem k1 2) (mul_mem (ofNat_mem _ 4) k2),
      nadd (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) i1) (nmul (nofNat 4) i2)⟩
  have hb4 : W.b₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.b₄‖ ≤ 1 := by
    unfold WeierstrassCurve.b₄
    exact ⟨add_mem (mul_mem (ofNat_mem _ 2) k4) (mul_mem k1 k3), nadd (nmul (nofNat 2) i4) (nmul i1 i3)⟩
  have hb6 : W.b₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.b₆‖ ≤ 1 := by
    unfold WeierstrassCurve.b₆
    exact ⟨add_mem (pow_mem k3 2) (mul_mem (ofNat_mem _ 4) k6),
      nadd (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) i3) (nmul (nofNat 4) i6)⟩
  obtain ⟨m2, n2⟩ := hb2
  obtain ⟨m4, n4⟩ := hb4
  obtain ⟨m6, n6⟩ := hb6
  have hc4 : W.c₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.c₄‖ ≤ 1 := by
    unfold WeierstrassCurve.c₄
    exact ⟨sub_mem (pow_mem m2 2) (mul_mem (ofNat_mem _ 24) m4),
      nsub (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) n2) (nmul (nofNat 24) n4)⟩
  have hc6 : W.c₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.c₆‖ ≤ 1 := by
    unfold WeierstrassCurve.c₆
    exact ⟨sub_mem (add_mem (neg_mem (pow_mem m2 3)) (mul_mem (mul_mem (ofNat_mem _ 36) m2) m4))
        (mul_mem (ofNat_mem _ 216) m6),
      nsub (nadd (by rw [norm_neg, norm_pow]; exact pow_le_one₀ (norm_nonneg _) n2)
        (nmul (nmul (nofNat 36) n2) n4)) (nmul (nofNat 216) n6)⟩
  have e12 := padic_norm_twelve_eq_one_of_five_le (p := p) h5
  have e216 := padicNorm_twoHundredSixteen_eq_one_of_five_le (p := p) h5
  have h12 : (12 : ℂ_[p]) ≠ 0 := by intro h; rw [h, norm_zero] at e12; exact zero_ne_one e12
  have h216 : (216 : ℂ_[p]) ≠ 0 := by intro h; rw [h, norm_zero] at e216; exact zero_ne_one e216
  refine ⟨div_mem hc4.1 (ofNat_mem _ 12), div_mem hc6.1 (ofNat_mem _ 216), ?_, ?_, ?_⟩
  · unfold Formalism.L2.Th1.A.g₂; rw [norm_div, e12, div_one]; exact hc4.2
  · unfold Formalism.L2.Th1.A.g₃; rw [norm_div, e216, div_one]; exact hc6.2
  · have hrel := W.c_relation
    have e : Formalism.L2.Th1.A.g₂ W ^ 3 - 27 * Formalism.L2.Th1.A.g₃ W ^ 2 = W.Δ := by
      unfold Formalism.L2.Th1.A.g₂ Formalism.L2.Th1.A.g₃
      have h1728 : (1728 : ℂ_[p]) = 12 ^ 3 := by norm_num
      field_simp
      linear_combination (-(216 : ℂ_[p]) ^ 2 * 12 ^ 3 / 1728 + 0) * hrel
    rw [e, hΔ]

end Int

theorem s2_in_unramified_closure (hTor : Formalism.L2.Th1.CM.CM4) (dK : ℕ) (L : PeriodPair) (hsq : Squarefree dK) (h4 : dK % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (l : ℕ) [Fact l.Prime] (hl5 : 5 ≤ l) (hld : ¬ l ∣ dK)
    (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]) (hlam : lam ≠ 0)
    (k2 : lam ^ 4 * ι L.g₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l) (k3 : lam ^ 6 * ι L.g₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l)
    (n2 : ‖lam ^ 4 * ι L.g₂‖ ≤ 1) (n3 : ‖lam ^ 6 * ι L.g₃‖ ≤ 1)
    (nd : ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1) :
    lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  have hlp : l.Prime := Fact.out
  have hd0 : 0 < dK := by omega
  obtain ⟨S, hS, -, -, hsum⟩ := Formalism.L2.Th1.F.hasCMByIsogeny dK L hcm (-1) 2 (by simp) hd0
  obtain ⟨hst, hns⟩ := Formalism.L2.Th1.F.hasCMByStable dK L hcm (-1) 2
  rw [Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq, hns] at hsum
  have hsum' : -(2 * (dK : ℂ)) * Formalism.L2.Th1.F.s2 L = ∑ P ∈ S, L.weierstrassP P := by
    rw [← hsum]; push_cast; ring
  have hP : ∀ P ∈ S, lam ^ 2 * ι (L.weierstrassP P) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
    intro P hPS
    obtain ⟨h1, h2⟩ := hS.1 P hPS
    have h3 : (dK : ℂ) * P ∈ L.lattice := by
      have h4' := hst _ h1
      have h5 : (dK : ℂ) * P
          = -((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK)
              * ((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) * P)) := by
        rw [← mul_assoc, ← sq, Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq]; ring
      rw [h5]; exact neg_mem h4'
    exact (hTor dK L hsq h4 hcm l hl5 hld ι lam hlam k2 k3 n2 n3 nd P dK hd0 hld h3 h2).1
  have hn : ¬ l ∣ 2 * dK := by
    intro h
    rcases (Nat.Prime.dvd_mul hlp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact hld h
  have hN : ‖((2 * dK : ℕ) : ℂ_[l])‖ = 1 :=
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hlp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one l) hn
  have hN0 : ((2 * dK : ℕ) : ℂ_[l]) ≠ 0 := by
    intro h; rw [h, norm_zero] at hN; exact zero_ne_one hN
  have key : lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L)
      = -(((2 * dK : ℕ) : ℂ_[l])⁻¹ * ∑ P ∈ S, lam ^ 2 * ι (L.weierstrassP P)) := by
    have h := congrArg ι hsum'
    rw [map_mul, map_neg, map_mul, map_sum, map_ofNat, map_natCast] at h
    rw [← Finset.mul_sum, ← h]
    push_cast
    push_cast at hN0
    have hd : (dK : ℂ_[l]) ≠ 0 := right_ne_zero_of_mul hN0
    field_simp
  rw [key]
  exact neg_mem (mul_mem (inv_mem (natCast_mem _ _)) (sum_mem fun P hPS => hP P hPS))

theorem cmLatticeInvariants_algebraic_of_goodReduction (hGood : Formalism.L2.Th1.CM.CM2) : Formalism.L2.KerInert.Sigma.InvAlg := by
  intro D cc δ hcurve hδ12 L hL
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12
  obtain ⟨-, hCM⟩ := GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc hδ
  have hL' : (L.lattice : Set ℂ) = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
  have hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcurve δ hδ12
    rw [← e2, ← e3]
    exact h
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
    intro ω hω
    have h1 := hCM ω (by rw [← hL]; exact hω)
    rw [← hL] at h1
    have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
      unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
    rw [e]; exact h1
  obtain ⟨p, hp5, hpp⟩ := Nat.exists_infinite_primes (D.host.d + 5)
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpd : ¬ p ∣ D.host.d := fun h => by have := Nat.le_of_dvd hdp.pos h; omega
  have hg2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    mem_algebraicClosure_iff.2
      (GlobalTheory.InertGenusOne.isAlgebraic_g2_of_hasCMBy_of_disc_eq_one hGood D.host.d L hdp.squarefree hd4 hcmby p (by omega) hpd hdisc)
  have hg3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    have h3sq : L.g₃ ^ 2 = (L.g₂ ^ 3 - 1) / 27 := by rw [← hdisc]; ring
    have hm : L.g₃ ^ 2 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
      rw [h3sq]
      have h27 : (27 : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
        have h : ((27 : ℕ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := natCast_mem _ 27
        simpa using h
      exact div_mem (sub_mem (pow_mem hg2 3) (one_mem _)) h27
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by norm_num : 0 < 2) (mem_algebraicClosure_iff.1 hm))
  exact ⟨hg2, hg3⟩

theorem wModel_Δ_lamOf (hInv : Formalism.L2.KerInert.Sigma.InvAlg) (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) :
    (Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)).Δ = 1 := by
  have hδ0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  obtain ⟨⟨L, hL⟩, -⟩ := GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc.1 hδ0
  have hL' : (L.lattice : Set ℂ) = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
  obtain ⟨h2, h3⟩ := hInv D cc δ hcc hδ L hL
  have hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
    rw [← e2, ← e3]
    exact h
  refine GlobalTheory.EvenTheta.DatumBasic.wModel_Δ lam (by rw [e2]; exact h2) (by rw [e3]; exact h3) ?_
  unfold Formalism.MainNotions.TaylorLogMetric.discr
  rw [e2, e3]
  exact hdisc

theorem frobExists : Formalism.L2.Th1.Top.FrobExistsH := by
  intro l _ hl
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.kurFrob l (by omega)
  exact ⟨σ, hσ⟩

section Cob

open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC LTIso beLT BeRat)
open Formalism.InvariantFactorPaths.G7 (cob at1)
open Formalism.L2.KerInert.BeCob (eLT)

theorem map_cob {K K' : Type} [Field K] [Field K'] (φ : K →+* K') (F : MvPowerSeries (Fin 2) K)
    (hF : MvPowerSeries.constantCoeff F = 0) (f : PowerSeries K) :
    MvPowerSeries.map φ (cob F f) = cob (MvPowerSeries.map φ F) (PowerSeries.map φ f) := by
  unfold cob at1
  rw [map_sub, map_sub, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)),
    MvPowerSeries.map_X, MvPowerSeries.map_X]

theorem cc_beLT {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (hb : BeRat g (eLT hLT))
    (hph : PowerSeries.constantCoeff g.ph = 0) : MvPowerSeries.constantCoeff (beLT hLT) = 0 := by
  have hex := hOk.2.2.1
  apply (k0ToC l).injective
  rw [map_zero, ← MvPowerSeries.constantCoeff_map]
  show MvPowerSeries.constantCoeff (MvPowerSeries.map (k0ToC l) (Formalism.L2.G.Pend.beOf g (eLT hLT))) = 0
  rw [Formalism.L2.G.Pend.map_beOf hb]
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (MvPowerSeries.C (eLT hLT)⁻¹ * MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) = 0 := by
    intro i
    rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hp0 := Formalism.MainNotions.J.cc_pt g hex (h0 0)
  have hp1 := Formalism.MainNotions.J.cc_pt g hex (h0 1)
  have hadd : MvPowerSeries.constantCoeff (g.add (g.pt (MvPowerSeries.C (eLT hLT)⁻¹ * MvPowerSeries.X 0))
      (g.pt (MvPowerSeries.C (eLT hLT)⁻¹ * MvPowerSeries.X 1)) : MvPowerSeries (Fin 2) ℂ_[l]) = 0 := by
    apply Formalism.MainNotions.J.cc_pt g hex
    rw [map_add, Formalism.MainNotions.J.cc_lg g hp0, Formalism.MainNotions.J.cc_lg g hp1, add_zero]
  unfold Formalism.L2.G.Pend.beC G1.be G1.phAt
  rw [map_sub, map_sub, PowerSeries.constantCoeff_subst_eq_zero hadd _ hph,
    PowerSeries.constantCoeff_subst_eq_zero hp0 _ hph, PowerSeries.constantCoeff_subst_eq_zero hp1 _ hph]
  simp

theorem ips {K : Type} [NormedField K] [IsUltrametricDist K] {f : PowerSeries K}
    (hf : Formalism.DworkPowerSeriesWeights.Integral (f : MvPowerSeries Unit K)) (k : ℕ) : ‖PowerSeries.coeff k f‖ ≤ 1 := hf _

end Cob

end GlobalTheory.CurveDictionary

namespace GlobalTheory.CurveDictionary

open NumberField Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1 At InertK ModelOverW)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF UnrOK IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.L2.KerInert.BeCob (eLT vLT psiLT)

theorem curveDict_of_inputs (hGood : Formalism.L2.Th1.CM.CM2) (hTor : Formalism.L2.Th1.CM.CM4)
    (hS2of : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic)
    (hCW : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ MaximalUnramifiedExtension p → W.a₂ ∈ MaximalUnramifiedExtension p →
      W.a₃ ∈ MaximalUnramifiedExtension p → W.a₄ ∈ MaximalUnramifiedExtension p → W.a₆ ∈ MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ MaximalUnramifiedExtension p →
      Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]))
    (hBC : Formalism.L2.KerInert.BeCob.BeCoef) (hCE : Formalism.L2.KerInert.BeCob.CobExact)
    (hCS : Formalism.L2.KerInert.BeCob.CobSimeq) (hPT : Formalism.L2.KerInert.BeCob.PhTie)
    (hTT : Formalism.L2.KerInert.BeCob.ThetaTie)
    (hVI : ∀ (l : ℕ) [Fact l.Prime] (g : G1 l), g.Ok → ∀ (hLT : LTIso g) (n : ℕ),
      ‖PowerSeries.coeff n (Formalism.L2.KerInert.BeCob.vLT hLT)‖ ≤ 1) :
    Formalism.L2.KerInert.Rep.CurveDict := by
  have hInv := cmLatticeInvariants_algebraic_of_goodReduction hGood
  have hS2 := hS2of hInv
  intro D cc δ l _ g hLT hAt h5 hIn hOW
  have hp : l.Prime := Fact.out
  obtain ⟨hcurve, -, hδ12, hLam, hOk⟩ := id hAt
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12
  obtain ⟨⟨L, hL⟩, hCM⟩ := GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc hδ
  have hLg : g.abelian₂ = L.lattice.toAddSubgroup := hLam.trans hL.symm
  obtain ⟨hg2, hg3⟩ := hInv D cc δ hcurve hδ12 L hL
  have hs := hS2 D cc δ hcurve hδ12 L hL
  set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3
  set s0 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨Formalism.L2.Th1.F.s2 L, hs⟩ with hs0
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)
  have hser : Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂ =
      Formalism.L2.Th1.B.sgStar (g.lam s0) (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [hLg]; exact sgSer_eq g.lam L a2 a3 s0 rfl rfl rfl
  have hW0 := wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  set εu : ℂ_[l] := ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) with hεu
  have hεne : εu ≠ 0 := Units.ne_zero _
  obtain ⟨c2, c3⟩ := g_change g.C (Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂)
  have gW2 : Formalism.L2.Th1.A.g₂ g.W = εu ^ 4 * g.lam a2 := by rw [← hW0.1]; exact c2
  have gW3 : Formalism.L2.Th1.A.g₃ g.W = εu ^ 6 * g.lam a3 := by rw [← hW0.2]; exact c3
  have hwp : Formalism.L2.Th1.A.wpReg g.W =
      PowerSeries.C (εu ^ 2) * PowerSeries.rescale εu (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [wpReg_eq, gW2, gW3]
    exact (Formalism.L2.Th1.F.seriesScale ℂ_[l] (g.lam a2) (g.lam a3) εu).2.2.2.1
  set s2 : ℂ_[l] := εu ^ 2 * g.lam s0 with hs2def
  have hR : PowerSeries.rescale εu (Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂) = PowerSeries.C εu * Formalism.L2.Th1.B.sgW g.W s2 := by
    unfold Formalism.L2.Th1.B.sgW
    rw [hser, hwp]
    exact ((Formalism.L2.Th1.F.sigmaScale ℂ_[l] (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) (g.lam s0) εu).2).symm
  have hph : g.ph = Formalism.L2.Th1.B.phW g.W s2 := Formalism.L2.KerInert.Dict.formal_phase_agree l g s2 hOk hR
  have hcc0 : PowerSeries.constantCoeff g.ph = 0 := by
    rw [hph]; exact (Formalism.L2.Th1.B.curveSigma ℂ_[l] g.W s2).1

  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending l g.lam
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hsqf : Squarefree D.host.d := hdp.squarefree
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hns : ¬ IsSquare ((-(D.host.d : ℤ) : ℤ) : ZMod l) := ZMod.nonsquare_of_jacobiSym_eq_neg_one hIn
  have hsq' : ¬ ∃ a : ZMod l, a ^ 2 = -(D.host.d : ZMod l) := by
    rintro ⟨a, ha⟩; apply hns; exact ⟨a, by push_cast; rw [← ha]; ring⟩
  have hpd : ¬ l ∣ D.host.d := by
    intro h; apply hsq'; refine ⟨0, ?_⟩
    rw [(ZMod.natCast_eq_zero_iff _ _).2 h]; ring
  have hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
    intro ω hω
    have h1 := hCM ω (by rw [← hL]; exact hω)
    rw [← hL] at h1
    have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
      unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
    rw [e]; exact h1
  have hιg2 : ι L.g₂ = g.lam a2 := hι a2
  have hιg3 : ι L.g₃ = g.lam a3 := hι a3
  have hιs : ι (Formalism.L2.Th1.F.s2 L) = g.lam s0 := hι s0
  obtain ⟨i1, i2, i3, i4, i6, hΔ⟩ := hOk.1
  obtain ⟨w1, w2, w3, w4, w6⟩ := hOW
  obtain ⟨k2, k3, n2, n3, nd⟩ := inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6
  have ks : s2 ∈ MaximalUnramifiedExtension l := by
    have k2' := k2; have k3' := k3; have n2' := n2; have n3' := n3; have nd' := nd
    rw [gW2, ← hιg2] at k2' n2'
    rw [gW3, ← hιg3] at k3' n3'
    rw [gW2, gW3, ← hιg2, ← hιg3] at nd'
    rw [hs2def, ← hιs]
    exact s2_in_unramified_closure hTor D.host.d L hsqf hd4 hcmby l h5 hpd ι εu hεne k2' k3' n2' n3' nd'
  have heW : eLT hLT ∈ Formalism.MainNotions.GL3Theta.Wp l := Formalism.L2.G.Pend.wToC_mem_Wp l _
  have he1 : ‖eLT hLT‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have ke : (eLT hLT)⁻¹ ∈ MaximalUnramifiedExtension l := inv_mem (wp_sub_kur _ heW)
  set G2 : MaximalUnramifiedExtension l := ⟨_, k2⟩ with hG2
  set G3 : MaximalUnramifiedExtension l := ⟨_, k3⟩ with hG3
  set S2 : MaximalUnramifiedExtension l := ⟨s2, ks⟩ with hS2d
  set E : MaximalUnramifiedExtension l := ⟨(eLT hLT)⁻¹, ke⟩ with hEd
  have hE1 : ‖E‖ = 1 := by
    show ‖(eLT hLT)⁻¹‖ = 1
    rw [norm_inv, he1, inv_one]
  have hth : ∀ n, ‖PowerSeries.coeff n (thetaS l G2 G3 E)‖ ≤ 1 := by
    intro n
    have hm := FAux.thetaS_map (MaximalUnramifiedExtension l).subtype (l := l) hp.two_le G2 G3 E
    rw [← FAux.norm_coe l, ← PowerSeries.coeff_map, hm]
    exact hTT l h5 g hLT hOk n

  have hgood : Formalism.L2.Th1.CM.IsGoodModel l L ι (G2 : ℂ_[l]) (G3 : ℂ_[l]) := by
    refine ⟨k2, k3, n2, n3, nd, εu, hεne, ?_, ?_⟩
    · show Formalism.L2.Th1.A.g₂ g.W = _
      rw [hιg2]; exact gW2
    · show Formalism.L2.Th1.A.g₃ g.W = _
      rw [hιg3]; exact gW3
  set c : ℂ := ι.symm εu⁻¹ with hcdef
  have hιc : ι c = εu⁻¹ := by rw [hcdef]; exact ι.apply_symm_apply _
  have hc : c ≠ 0 := by
    intro h0; rw [h0, map_zero] at hιc; exact inv_ne_zero hεne hιc.symm
  obtain ⟨-, -, -, -, -, -, hs2c, -, -, hg2c, hg3c⟩ := Formalism.L2.Th1.F.homogeneity L c hc
  have h2c : (G2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ := by
    show Formalism.L2.Th1.A.g₂ g.W = _
    rw [hg2c, map_mul, map_inv₀, map_pow, hιc, hιg2, gW2, inv_pow, inv_inv]
  have h3c : (G3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ := by
    show Formalism.L2.Th1.A.g₃ g.W = _
    rw [hg3c, map_mul, map_inv₀, map_pow, hιc, hιg3, gW3, inv_pow, inv_inv]
  have hsc : (S2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) := by
    show s2 = _
    rw [hs2c, map_mul, map_inv₀, map_pow, hιc, hιs, hs2def, inv_pow, inv_inv]
  have hNR : ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
      ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l G2 G3 S2 E) α := by
    intro σ hσ α hα hσα
    have hw := (sqrtKur D.host.d hsqf hd4 l h5 hsq' ι).1
    have hmem : ∀ m n : ℤ, ι ((m : ℂ) + (n : ℂ) * omegaK D.host.d) ∈ MaximalUnramifiedExtension l := by
      intro m n
      rw [map_add, map_mul, map_intCast, map_intCast]
      exact add_mem (intCast_mem _ m) (mul_mem (intCast_mem _ n) hw)
    let S : Set (MaximalUnramifiedExtension l) := {a | ∃ m n : ℤ, ¬ (l : ℤ) ∣ normInt D.host.d m n ∧
      (a : ℂ_[l]) = ι ((m : ℂ) + (n : ℂ) * omegaK D.host.d)}
    refine normUnits (MaximalUnramifiedExtension l) l σ hσ (phFF l G2 G3 S2 E) (FAux.cc_phFF (by omega) _ _ _ _) S ?_ α ?_
    · rintro a ⟨m, n, hmn, ha⟩
      exact nrDense hTor D.host.d L hsqf hd4 hcmby l h5 hpd hsq' ι G2 G3 E S2 hgood hE1 hth
        c hc h2c h3c hsc σ hσ m n hmn a ha
    · intro e he
      obtain ⟨m, n, hmn, hclose⟩ := denseOK D.host.d hsqf hd4 l h5 hsq' ι σ hσ α hα hσα e he
      exact ⟨⟨_, hmem m n⟩, ⟨m, n, hmn, rfl⟩, by simpa using hclose⟩

  have hBR : BeRat g (eLT hLT) := by
    have hphW : Formalism.MainNotions.GL3Theta.CoefWf g.ph := by
      rw [hph]
      exact hCW l g.W (wp_sub_kur _ w1) (wp_sub_kur _ w2) (wp_sub_kur _ w3) (wp_sub_kur _ w4) (wp_sub_kur _ w6) s2 ks
    have hB := hBC l g hOk ⟨w1, w2, w3, w4, w6⟩ hphW
    show BeRat g (wToC l (epOf hLT : Formalism.MainNotions.FormalGroupSystem.WW l))
    rw [← Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap l]
    exact Formalism.L2.G.Pend.beRat_of g hOk.2.2.1 hB (Formalism.L2.G.Pend.exRat_of g hOk ⟨w1, w2, w3, w4, w6⟩) _
  obtain ⟨σ0, hσ0⟩ := frobExists l h5
  obtain ⟨F0, hF0⟩ := (Formalism.InvariantFactorPaths.G7.Top.lawExists (MaximalUnramifiedExtension l) l hσ0.1 hσ0.2.2.1).1
  have tie : ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.map (k0ToC l) (inParam l (beLT hLT)))
        (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l G2 G3 S2 E))) := by
    intro F hF
    rw [hCE l g hLT hOk hBR F hF, map_cob (MaximalUnramifiedExtension l).subtype F hF.1,
      Formalism.L2.Th1.E.Joints.map_phFF (MaximalUnramifiedExtension l).subtype hp.two_le]
    refine hCS ℂ_[l] _ (by rw [MvPowerSeries.constantCoeff_map, hF.1, map_zero]) ?_ _ _ (hPT l g hLT hOk s2 hph)
    intro n
    rw [MvPowerSeries.coeff_map]
    exact hF.2.1 n

  have hlamg : g.abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := hLam
  have hΔW : g.W.Δ = εu ^ 12 := by
    show (g.C • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂).Δ = εu ^ 12
    rw [WeierstrassCurve.variableChange_Δ, hlamg,
      wModel_Δ_lamOf hInv D cc δ hcurve hδ12 g.lam, mul_one]
  have hΔ1 : ‖g.W.Δ‖ = 1 := hOk.1.2.2.2.2.2
  have hεu1 : ‖εu‖ = 1 := by
    have := hΔ1
    rw [hΔW, norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hnorm : ‖εu * (eLT hLT)⁻¹‖ = 1 := by rw [norm_mul, norm_inv, he1, hεu1, inv_one, one_mul]

  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq g.W.Δ (show 0 < 12 by norm_num)
  have hν1 : ‖ν‖ = 1 := by
    have := congrArg norm hν
    rw [norm_pow, hΔ1] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hν0 : ν ≠ 0 := by
    intro h; rw [h, norm_zero] at hν1; exact zero_ne_one hν1
  have hp2 : l ≠ 2 := by omega
  set C' := scC ν hν0 * g.C with hC'
  set wq' := PowerSeries.rescale ν⁻¹ g.wq with hwq'
  have hC'W : C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂ = scC ν hν0 • g.W := mul_smul _ _ _
  have hM : Formalism.MainNotions.TaylorLogMetric.IsModel g.lam g.abelian₂ C' :=
    isModel_scale g.lam g.abelian₂ g.C hOk.1 ν hν0 hν1 hν
  have hWq : Formalism.MainNotions.TaylorLogMetric.IsWq (C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂) wq' := by
    rw [hC'W]; exact isWq_scale ν hν0 _ _ hOk.2.1

  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set v := vLT hLT with hvdef
  set A : PowerSeries ℂ_[l] := PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l with hAdef
  have hA0 : PowerSeries.constantCoeff A = 0 := by rw [hAdef, map_mul, cc_lgF', mul_zero]
  have hAs : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  have hexs : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hv0 : PowerSeries.constantCoeff v = 0 := by
    rw [hvdef, vLT]
    exact PowerSeries.constantCoeff_subst_eq_zero hA0 _ hex
  have hvs : PowerSeries.HasSubst v := PowerSeries.HasSubst.of_constantCoeff_zero' hv0
  have hvl : PowerSeries.subst v g.l = A := by
    rw [hvdef, vLT, ← hAdef, ← PowerSeries.subst_comp_subst_apply hexs hAs, hinv, PowerSeries.subst_X hAs]
  set hh : PowerSeries ℂ_[l] := PowerSeries.C ν * v with hhdef
  have hh0 : PowerSeries.constantCoeff hh = 0 := by rw [hhdef, map_mul, hv0, mul_zero]
  have hhI : ∀ n, Formalism.MainNotions.TaylorLogMetric.IsIntP (PowerSeries.coeff n hh) := by
    intro n
    unfold Formalism.MainNotions.TaylorLogMetric.IsIntP
    rw [hhdef, PowerSeries.coeff_C_mul, norm_mul, hν1, one_mul]
    exact hVI l g hOk hLT n
  have hlog : PowerSeries.subst hh (Formalism.MainNotions.TaylorLogMetric.flog (C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂) wq') =
      PowerSeries.C (ν * (eLT hLT)⁻¹) * PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) := by
    have hs : PowerSeries.HasSubst hh := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
    rw [hC'W, hwq', flog_scale ν hν0, ← PowerSeries.smul_eq_C_mul,
      PowerSeries.subst_smul hs, hhdef, subst_Cmul_rescale ν hν0 v _ hv0]
    change ν • PowerSeries.subst v g.l = _
    rw [hvl, hAdef, lgF_eq_logF, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul]

  set phC : PowerSeries ℂ_[l] := phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 (eLT hLT)⁻¹ with hphC
  have hphL : Formalism.L2.Th1.Top.phL l G2 G3 S2 E = phC := by
    unfold Formalism.L2.Th1.Top.phL
    rw [Formalism.L2.Th1.E.Joints.map_phFF (MaximalUnramifiedExtension l).subtype hp.two_le]
    rfl
  have hphC0 : PowerSeries.constantCoeff phC = 0 := by
    rw [← hphL]; unfold Formalism.L2.Th1.Top.phL
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF (by omega) _ _ _ _, map_zero]
  set ψ : PowerSeries ℂ_[l] := psiLT hLT with hψdef
  have hψ0 : PowerSeries.constantCoeff ψ = 0 := by
    rw [hψdef, psiLT]; exact PowerSeries.constantCoeff_subst_eq_zero hv0 _ hcc0
  have hsym := (Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[l] Unit).2.1 _ _ (hPT l g hLT hOk s2 hph)
  set V : PowerSeries ℂ_[l] := Formalism.L2.Th1.C.mvExp (phC - ψ) with hVdef
  have hV : ∀ n, Formalism.MainNotions.TaylorLogMetric.IsIntP (PowerSeries.coeff n V) := fun n => ips hsym.2 n
  have hsubE : PowerSeries.subst hh (Formalism.MainNotions.TaylorLogMetric.ePhi1 g.lam g.abelian₂ C' wq') = Formalism.L2.Th1.C.mvExp (-ψ) := by
    rw [hC', hwq', ePhi1_scale, hhdef,
      subst_Cmul_rescale ν hν0 v _ hv0, Formalism.L2.KerInert.Dict.ePhi1_eq g s2 hOk hR, ← hph]
    have hn : PowerSeries.constantCoeff (-g.ph) = 0 := by rw [map_neg, hcc0, neg_zero]
    change PowerSeries.subst v (Formalism.L2.Th1.C.mvExp (-g.ph) : PowerSeries ℂ_[l]) = _
    rw [Formalism.L2.Th1.C.subst_mvExp hn hv0, hψdef, psiLT, ← PowerSeries.coe_substAlgHom hvs, map_neg]
  have hexp : (Formalism.L2.Th1.C.mvExp phC : PowerSeries ℂ_[l]) =
      V * (PowerSeries.subst hh (Formalism.MainNotions.TaylorLogMetric.ePhi1 g.lam g.abelian₂ C' wq'))⁻¹ := by
    have hn : PowerSeries.constantCoeff (Formalism.L2.Th1.C.mvExp (-ψ) : PowerSeries ℂ_[l]) ≠ 0 := by
      have h1 := Formalism.L2.Th1.C.constantCoeff_mvExp (show MvPowerSeries.constantCoeff (-ψ : PowerSeries ℂ_[l]) = 0 by
        rw [map_neg]; exact (neg_eq_zero.mpr hψ0))
      intro h0
      exact one_ne_zero (h1.symm.trans h0)
    have hinvE : (Formalism.L2.Th1.C.mvExp ψ : PowerSeries ℂ_[l]) = (Formalism.L2.Th1.C.mvExp (-ψ) : PowerSeries ℂ_[l])⁻¹ :=
      (PowerSeries.eq_inv_iff_mul_eq_one hn).mpr (Formalism.L2.Th1.C.mvExp_mul_neg hψ0)
    rw [hsubE, ← hinvE, hVdef]
    exact (Formalism.L2.Th1.C.mvExp_sub_mul hphC0 hψ0).symm
  have hcEq : (((C'.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l])) * (ν * (eLT hLT)⁻¹) = εu * (eLT hLT)⁻¹ := by
    rw [hC', scC_mul_uinv, ← hεu]
    field_simp
  refine ⟨G2, G3, E, S2, rfl, rfl, rfl, hR, hnorm,
    ⟨n2, n3, hE1, hth, hNR, cc_beLT hOk hLT hBR hcc0, F0, hF0, tie F0 hF0⟩, ?_⟩
  intro D'
  refine ⟨C', wq', hM, hWq, ?_⟩
  intro N N' r b G hInt
  have key := dict_core hp2 D' g.lam g.abelian₂ C' wq' hh hh0 hhI (ν * (eLT hLT)⁻¹) hlog
    phC V hphC0 hV hexp b G hInt
  rw [hcEq] at key
  rw [hphL]
  exact key

end GlobalTheory.CurveDictionary
