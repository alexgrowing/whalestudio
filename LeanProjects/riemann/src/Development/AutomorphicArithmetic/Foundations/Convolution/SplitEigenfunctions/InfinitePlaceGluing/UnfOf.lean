import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.WhittakerHecke.IdeleCoveringLintegralEqConstMulHaar
import Development.AutomorphicArithmetic.WhittakerHecke.UnfoldedIntegrandMeasurableIntegrableOfReGtFour
import Development.AutomorphicArithmetic.WhittakerHecke.IntegralTsumIdeleCoveringEqConstMul
import Development.AutomorphicArithmetic.WhittakerHecke.IntegralUnfoldedIntegrandEqZetaIntegral
import Development.AutomorphicArithmetic.WhittakerHecke.SetIntegralRestrictMulThetaKernelEqUnfolded
import Development.AutomorphicArithmetic.WhittakerHecke.TsumUnfoldedIntegrandIdeleCoveringEqExpMul

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.unf_of :
    Unf := by
  intro E _ _ _ D P ω χ hC hω hχ M U
  haveI := M.prob
  haveI := U.prob
  obtain ⟨c, hc0, hc⟩ := UpperTheory.ideleCovering_lintegral_eq_const_mul_haar U
  refine ⟨(c : ℂ), by exact_mod_cast hc0, ?_⟩
  intro φ hA Φ hΦ s hs
  obtain ⟨hm, hI⟩ := UpperTheory.unfoldedIntegrand_measurable_integrable_of_re_gt_four E D ω χ φ hA hω hχ M Φ hΦ s hs
  obtain ⟨hsum, heq⟩ := UpperTheory.integral_tsum_ideleCovering_eq_const_mul U c hc M.κ (Un.Hh D χ φ Φ s) hm hI
  rw [← UpperTheory.integral_unfoldedIntegrand_eq_zetaIntegral E D χ φ M Φ s hI, ← heq]
  unfold Zs Ir
  refine integral_congr_ae ?_
  have hUU : ∀ᵐ u ∂U.υ, u ∈ UU := mem_ae_iff.2 U.supp
  filter_upwards [hsum] with t ht
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ht, hUU] with u hu huU
  rw [UpperTheory.setIntegral_restrict_mul_thetaKernel_eq_unfolded E D ω φ hA M Φ hΦ t u huU, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hu] with p hp
  exact UpperTheory.tsum_unfoldedIntegrand_ideleCovering_eq_exp_mul E D ω χ φ hA hχ Φ s t u huU p hp
