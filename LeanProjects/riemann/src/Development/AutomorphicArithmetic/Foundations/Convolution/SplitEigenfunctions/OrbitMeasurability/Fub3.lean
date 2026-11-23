import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ContInfPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
open scoped Classical

private theorem fub3 {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [Countable Z]
    [MeasurableSingletonClass Z] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (f : X × Y × Z → ℂ)
    (hf : Integrable f (μ.prod (ν.prod Measure.count))) :
    ∫ p, f p ∂(μ.prod (ν.prod Measure.count)) = ∫ x, ∫ y, ∑' z, f (x, y, z) ∂ν ∂μ := by
  rw [integral_prod _ hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with x hx
  rw [integral_prod _ hx]
  refine integral_congr_ae ?_
  filter_upwards [hx.prod_right_ae] with y hy
  rw [integral_countable hy]
  simp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.yEq :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.YEq := by
  intro E _ _ _ D W M N P φ hφ ph hph
  haveI := N.haar
  haveI : SigmaFinite N.μ := inferInstance
  obtain ⟨hp, hw, hint⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.yInt E D W M N P φ hφ
  obtain ⟨hc, K, hK, hB⟩ := UpperTheory.ConvolutionTheory.R2.Ff.wtBound ℚ ph
  obtain ⟨n, hn⟩ := hint K hK
  obtain ⟨B, hB⟩ := hB n
  obtain ⟨-, -, h1, h2, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  have hI : Integrable (fun y => ph.1 (pY D y) * φ.1 (el D y)) (mY D.δ N) := by
    refine (hn.norm.const_mul B).mono' ((hc.measurable.comp hp).mul hw).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ wt K n (pY D y) := by
      unfold wt
      split_ifs
      · positivity
      · exact le_rfl
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hB () trivial _) (norm_nonneg _)
  unfold mY at hI ⊢
  rw [fub3 _ _ _ hI]
  unfold fOn J1 UI mean ThOn
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  have hnu : nu ℚ (gl h * sZ D (z : IdeleGroup E)) = 1 := by
    have a := h1 (z : IdeleGroup E)
    have b := h2 h
    unfold nu at a b ⊢
    rw [map_mul, map_mul, a, b, one_mul]
  have hab : ab (1 : (A ℚ)ˣ) = 1 := by
    unfold ab
    have : IdeleGroup.ideleModule ℚ (1 : (A ℚ)ˣ) = 1 := map_one _
    rw [this]
    rfl
  simp only [el, pY]
  rw [tsum_mul_right]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [map_one, Module.End.one_apply, W.L_apply, hnu, hab]
  simp
