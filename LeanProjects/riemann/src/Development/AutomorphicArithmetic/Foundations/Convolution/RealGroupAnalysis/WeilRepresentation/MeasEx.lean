import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BorHomeo
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BorHaar
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CptMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Unimod
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Iwa
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.measEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], St.MeasEx F := by
  intro F _ _ _
  obtain ⟨hK, hKc⟩ := M.kkCpt F
  obtain ⟨hB, e, he⟩ := M.borHomeo F
  obtain ⟨μS, hS, hSi⟩ := M.borHaar F
  obtain ⟨μK, hμK, hp, hsupp, hl, hr⟩ := M.cptMeas (G1 F) (M.Ks F) (hK ▸ hKc)
  let μ₀ : Measure (G1 F) := Measure.haar
  haveI := M.unimod F μ₀
  have hsurj : Function.Surjective (HaarSK.mulMap (M.Bor F) (M.Ks F)) := by
    intro g
    obtain ⟨b, a, k, hk, rfl⟩ := M.iwa F g
    refine ⟨(e (a, b), ⟨k, by rw [← SetLike.mem_coe, ← hK]; exact hk⟩), ?_⟩
    change (e (a, b) : G1 F) * k = _
    rw [he]
  obtain ⟨c, hc, hint⟩ := HaarSK.exists_lintegral_eq μ₀ hB (hK ▸ hKc) hsurj μS μK
  have hc' : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
  let μ : Measure (G1 F) := (c : ℝ≥0∞)⁻¹ • μ₀
  haveI hμ : μ.IsHaarMeasure :=
    Measure.IsHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) (ENNReal.inv_ne_top.2 hc')
  obtain ⟨D, hD, hDu, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Gam F)
  haveI : CompactSpace (M.Ks F) := isCompact_iff_compactSpace.1 (hK ▸ hKc)
  haveI : LocallyCompactSpace (M.Bor F) := hB.locallyCompactSpace
  haveI : SecondCountableTopology (M.Bor F) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (M.Ks F) := TopologicalSpace.Subtype.secondCountableTopology _
  refine ⟨⟨μ, μK.map Subtype.val, D, hμ, M.unimod F μ,
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable, hK ▸ hsupp,
    fun k hk => hl k (by rw [← SetLike.mem_coe, ← hK]; exact hk),
    fun k hk => hr k (by rw [← SetLike.mem_coe, ← hK]; exact hk), fun u hu => ?_, hD,
    IsFundamentalDomain.mk' hD.nullMeasurableSet hDu⟩⟩
  have hm : Measurable fun p : M.Bor F × G1 F => u ((p.1 : G1 F) * p.2) :=
    hu.comp ((continuous_subtype_val.comp continuous_fst).mul continuous_snd).measurable
  have h1 : ∀ k : G1 F, ∫⁻ a : IdeleGroup F, ∫⁻ b, u (nU b * mD a * k) * ENNReal.ofReal ((ab a)⁻¹ ^ 2) ∂(adeleMeasure F) ∂(ideleMeasure F) =
      ∫⁻ s : M.Bor F, u ((s : G1 F) * k) ∂μS := fun k =>
    (hSi (fun g => u (g * k)) (hu.comp (measurable_mul_const k))).symm
  simp only [h1]
  rw [lintegral_map hm.lintegral_prod_left' measurable_subtype_coe, lintegral_smul_measure, hint u hu, smul_eq_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel hc' ENNReal.coe_ne_top, one_mul]
  exact lintegral_lintegral_swap (hm.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))).aemeasurable
