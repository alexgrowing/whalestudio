import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqLevi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem LeviCompHol.proof : LeviCompHol.Statement := by
  intro E F _ _ g φ x w hg hφ
  have hgev : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ g y := hg.eventually_analyticAt
  have hfdg : ∀ᶠ y in 𝓝 x, fderiv ℝ g y = (fderiv ℂ g y).restrictScalars ℝ := by
    filter_upwards [hgev] with y hy
    exact hy.differentiableAt.fderiv_restrictScalars ℝ
  have hgC : ContDiffAt ℂ 2 g x := hg.contDiffAt
  have hgR : ContDiffAt ℝ 2 g x := hgC.restrict_scalars ℝ
  have hgd : DifferentiableAt ℝ g x := hgR.differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hgR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hGw : ∀ v, fderiv ℝ g x v = fderiv ℂ g x v := fun v => by rw [hfdg.self_of_nhds]; rfl
  have hGI : ∀ v, fderiv ℝ g x (Complex.I • v) = Complex.I • fderiv ℝ g x v := fun v => by
    rw [hGw, hGw]; exact (fderiv ℂ g x).map_smul _ _

  have hG2I : ∀ u v, fderiv ℝ (fderiv ℝ g) x u (Complex.I • v) =
      Complex.I • fderiv ℝ (fderiv ℝ g) x u v := by
    intro u v
    have hA : HasFDerivAt (fun y => fderiv ℝ g y (Complex.I • v))
        ((ContinuousLinearMap.apply ℝ (F → ℂ) (Complex.I • v)).comp (fderiv ℝ (fderiv ℝ g) x)) x :=
      (ContinuousLinearMap.apply ℝ (F → ℂ) (Complex.I • v)).hasFDerivAt.comp x hd2.hasFDerivAt
    have hB : HasFDerivAt (fun y => Complex.I • fderiv ℝ g y v)
        (Complex.I • (ContinuousLinearMap.apply ℝ (F → ℂ) v).comp (fderiv ℝ (fderiv ℝ g) x)) x :=
      ((ContinuousLinearMap.apply ℝ (F → ℂ) v).hasFDerivAt.comp x hd2.hasFDerivAt).const_smul Complex.I
    have hAB : (fun y => Complex.I • fderiv ℝ g y v) =ᶠ[𝓝 x] fun y => fderiv ℝ g y (Complex.I • v) := by
      filter_upwards [hfdg] with y hy
      rw [hy]; exact ((fderiv ℂ g y).map_smul _ _).symm
    have h := congrArg (fun L => L u) ((hB.congr_of_eventuallyEq hAB.symm).unique hA)
    simpa using h.symm
  have hsymm : IsSymmSndFDerivAt ℝ g x := hgR.isSymmSndFDerivAt (by simp)
  have hG2II : fderiv ℝ (fderiv ℝ g) x (Complex.I • w) (Complex.I • w) =
      -fderiv ℝ (fderiv ℝ g) x w w := by
    rw [hG2I, hsymm (Complex.I • w) w, hG2I, smul_smul, Complex.I_mul_I, neg_one_smul]
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 φ (g y) :=
    hgd.continuousAt.tendsto.eventually (hφ.eventually (by simp))
  have hfd : fderiv ℝ (fun y => φ (g y)) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ φ (g y)).comp (fderiv ℝ g y) := by
    filter_upwards [hev, hgev] with y hy hy'
    exact fderiv_comp y (hy.differentiableAt (by norm_num)) (hy'.differentiableAt.restrictScalars ℝ)
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) (g x) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y => fderiv ℝ φ (g y))
      ((fderiv ℝ (fderiv ℝ φ) (g x)).comp (fderiv ℝ g x)) x :=
    hdφ.hasFDerivAt.comp x hgd.hasFDerivAt
  have hD := hc.clm_comp hd2.hasFDerivAt
  unfold leviForm
  rw [hfd.fderiv_eq, hD.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, hGI, hG2II, map_neg, hGw]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
