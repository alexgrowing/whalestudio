import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMRead
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ExistsWittSeriesInverseFormalGroupIso
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsModel

noncomputable section

namespace Formalism.L2.KerInert.WeierstrassScaling

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
    rw [hL, Formalism.L2.KerInert.BeCob.lgF_eq_logF]; exact Formalism.L2.KerInert.BeCob.cc_lgF' _ _
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

end Formalism.L2.KerInert.WeierstrassScaling

namespace Formalism.L2.KerInert.BeCob

open NumberField Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1 At InertK ModelOverW)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF UnrOK IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)
open Formalism.DworkPowerSeriesWeights (Integral)

theorem rdictMain : Formalism.L2.KerInert.Rep.CurveDict := by
  have hInv := Sigma.invAlg'
  have hS2 := Sigma.secondEisensteinAlgebraic
  have hPhW : PhWAll := Dict.phWAll_of (Sigma.sigmaCurveInert_of Sigma.invAlg' Sigma.secondEisensteinAlgebraic)
  have hBC := beta_coefficients
  have hCE := coboundary_exact
  have hCS := coboundary_equivalence
  have hPT := phase_compatibility
  have hTT := thetaTie_of short_exact_isomorphism
  intro D cc δ l _ g hLT hAt h5 hIn hOW
  have hp : l.Prime := Fact.out
  obtain ⟨hcurve, -, hδ12, hLam, hOk⟩ := id hAt
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := by
    intro h0
    obtain ⟨⟨L1, hL1⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc 1 hcc one_ne_zero
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L1 (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL1)
    have hd := Formalism.L2.Th1.F.discNeZero L1
    apply hd
    have h12 := hδ12
    unfold Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice Formalism.MainNotions.TaylorLogMetric.discr at h12
    rw [h0, e2, e3] at h12
    rw [← h12]; norm_num
  obtain ⟨⟨L, hL⟩, hCM⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ
  have hLg : g.abelian₂ = L.lattice.toAddSubgroup := hLam.trans hL.symm
  obtain ⟨hg2, hg3⟩ := hInv D cc δ hcurve hδ12 L hL
  have hs := hS2 D cc δ hcurve hδ12 L hL
  set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3
  set s0 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨Formalism.L2.Th1.F.s2 L, hs⟩ with hs0
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)
  have hser : Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂ =
      Formalism.L2.Th1.B.sgStar (g.lam s0) (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [hLg]; exact Sigma.sgSer_eq g.lam L a2 a3 s0 rfl rfl rfl
  have hW0 := Sigma.wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  set εu : ℂ_[l] := ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) with hεu
  have hεne : εu ≠ 0 := Units.ne_zero _
  obtain ⟨c2, c3⟩ := Sigma.g_change g.C (Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂)
  have gW2 : Formalism.L2.Th1.A.g₂ g.W = εu ^ 4 * g.lam a2 := by rw [← hW0.1]; exact c2
  have gW3 : Formalism.L2.Th1.A.g₃ g.W = εu ^ 6 * g.lam a3 := by rw [← hW0.2]; exact c3
  have hwp : Formalism.L2.Th1.A.wpReg g.W =
      PowerSeries.C (εu ^ 2) * PowerSeries.rescale εu (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [Sigma.wpReg_eq, gW2, gW3]
    exact (Formalism.L2.Th1.F.seriesScale ℂ_[l] (g.lam a2) (g.lam a3) εu).2.2.2.1
  set s2 : ℂ_[l] := εu ^ 2 * g.lam s0 with hs2def
  have hR : PowerSeries.rescale εu (Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂) = PowerSeries.C εu * Formalism.L2.Th1.B.sgW g.W s2 := by
    unfold Formalism.L2.Th1.B.sgW
    rw [hser, hwp]
    exact ((Formalism.L2.Th1.F.sigmaScale ℂ_[l] (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) (g.lam s0) εu).2).symm
  have hph : g.ph = Formalism.L2.Th1.B.phW g.W s2 := Dict.formal_phase_agree l g s2 hOk hR
  have hcc0 : PowerSeries.constantCoeff g.ph = 0 := by
    rw [hph]; exact (Formalism.L2.Th1.B.curveSigma ℂ_[l] g.W s2).1

  obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt l g.lam
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
  obtain ⟨k2, k3, n2, n3, nd⟩ := Sigma.inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6
  have ks : s2 ∈ MaximalUnramifiedExtension l := by
    have k2' := k2; have k3' := k3; have n2' := n2; have n3' := n3; have nd' := nd
    rw [gW2, ← hιg2] at k2' n2'
    rw [gW3, ← hιg3] at k3' n3'
    rw [gW2, gW3, ← hιg2, ← hιg3] at nd'
    rw [hs2def, ← hιs]
    exact Sigma.s2_in_unramified_closure D.host.d L hsqf hd4 hcmby l h5 hpd ι εu hεne k2' k3' n2' n3' nd'
  have heW : eLT hLT ∈ Formalism.MainNotions.GL3Theta.Wp l := Formalism.L2.G.Pend.wToC_mem_Wp l _
  have he1 : ‖eLT hLT‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have ke : (eLT hLT)⁻¹ ∈ MaximalUnramifiedExtension l := inv_mem (Sigma.wp_sub_kur _ heW)
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
      exact nrDense Formalism.L2.Th1.CM.cm4 D.host.d L hsqf hd4 hcmby l h5 hpd hsq' ι G2 G3 E S2 hgood hE1 hth
        c hc h2c h3c hsc σ hσ m n hmn a ha
    · intro e he
      obtain ⟨m, n, hmn, hclose⟩ := denseOK D.host.d hsqf hd4 l h5 hsq' ι σ hσ α hα hσα e he
      exact ⟨⟨_, hmem m n⟩, ⟨m, n, hmn, rfl⟩, by simpa using hclose⟩

  have hBR : BeRat g (eLT hLT) := by
    have hphW := hPhW D l cc δ g hAt h5 hIn ⟨w1, w2, w3, w4, w6⟩
    have hB := hBC l g hOk ⟨w1, w2, w3, w4, w6⟩ hphW
    show BeRat g (wToC l (epOf hLT : Formalism.MainNotions.FormalGroupSystem.WW l))
    rw [← Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap l]
    exact Formalism.L2.G.Pend.beRat_of g hOk.2.2.1 hB (Formalism.L2.G.Pend.exRat_of g hOk ⟨w1, w2, w3, w4, w6⟩) _
  obtain ⟨σ0, hσ0⟩ := Formalism.L2.Th1.Top.frobExistsH l h5
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
      Formalism.L2.KerInert.JetsModel.wModel_Δ D cc δ hcurve hδ12 g.lam, mul_one]
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
  set C' := Formalism.L2.KerInert.WeierstrassScaling.scC ν hν0 * g.C with hC'
  set wq' := PowerSeries.rescale ν⁻¹ g.wq with hwq'
  have hC'W : C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂ = Formalism.L2.KerInert.WeierstrassScaling.scC ν hν0 • g.W := mul_smul _ _ _
  have hM : Formalism.MainNotions.TaylorLogMetric.IsModel g.lam g.abelian₂ C' :=
    Formalism.L2.KerInert.WeierstrassScaling.isModel_scale g.lam g.abelian₂ g.C hOk.1 ν hν0 hν1 hν
  have hWq : Formalism.MainNotions.TaylorLogMetric.IsWq (C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂) wq' := by
    rw [hC'W]; exact Formalism.L2.KerInert.WeierstrassScaling.isWq_scale ν hν0 _ _ hOk.2.1

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
    exact v_integral hOk hLT n
  have hlog : PowerSeries.subst hh (Formalism.MainNotions.TaylorLogMetric.flog (C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂) wq') =
      PowerSeries.C (ν * (eLT hLT)⁻¹) * PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) := by
    have hs : PowerSeries.HasSubst hh := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
    rw [hC'W, hwq', Formalism.L2.KerInert.WeierstrassScaling.flog_scale ν hν0, ← PowerSeries.smul_eq_C_mul,
      PowerSeries.subst_smul hs, hhdef, Formalism.L2.KerInert.WeierstrassScaling.subst_Cmul_rescale ν hν0 v _ hv0]
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
    rw [hC', hwq', Formalism.L2.KerInert.WeierstrassScaling.ePhi1_scale, hhdef,
      Formalism.L2.KerInert.WeierstrassScaling.subst_Cmul_rescale ν hν0 v _ hv0, Dict.ePhi1_eq g s2 hOk hR, ← hph]
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
    rw [hC', Formalism.L2.KerInert.WeierstrassScaling.scC_mul_uinv, ← hεu]
    field_simp
  refine ⟨G2, G3, E, S2, rfl, rfl, rfl, hR, hnorm,
    ⟨n2, n3, hE1, hth, hNR, cc_beLT hOk hLT hBR hcc0, F0, hF0, tie F0 hF0⟩, ?_⟩
  intro D'
  refine ⟨C', wq', hM, hWq, ?_⟩
  intro N N' r b G hInt
  have key := Formalism.L2.KerInert.WeierstrassScaling.dict_core hp2 D' g.lam g.abelian₂ C' wq' hh hh0 hhI (ν * (eLT hLT)⁻¹) hlog
    phC V hphC0 hV hexp b G hInt
  rw [hcEq] at key
  rw [hphL]
  exact key

end Formalism.L2.KerInert.BeCob

namespace Formalism.L2.KerInert.Rep

theorem curve_dictionary : CurveDict := Formalism.L2.KerInert.BeCob.rdictMain

end Formalism.L2.KerInert.Rep
