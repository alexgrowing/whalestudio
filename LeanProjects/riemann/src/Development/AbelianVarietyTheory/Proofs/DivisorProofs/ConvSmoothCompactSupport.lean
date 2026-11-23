import Mathlib
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvLeOfSupportCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothFunIntegralMulRightStatement
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.ConvSmooth

theorem secondCountable_units (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] : SecondCountableTopology 𝔸ˣ := by
  haveI : ProperSpace 𝔸 := FiniteDimensional.proper ℝ 𝔸
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem isSmoothFun_density {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) {L : Set G} (hL : IsCompact L)
    {κ : G → ℂ} (hκ : h.IsSmoothFun κ) {p : G → NNReal} (hp : Measurable p)
    (hpi : Integrable (fun y => (p y : ℝ)) μ) (hpL : ∀ y ∉ L, p y = 0) :
    h.IsSmoothFun (fun z => ∫ y, κ (z * y) * ((p y : ℝ) : ℂ) ∂μ) := by
  set ν := μ.withDensity (fun y => (p y : ENNReal)) with hν
  have hlt : ∫⁻ y, (p y : ENNReal) ∂μ < ⊤ := by
    have := hpi.lintegral_lt_top
    simpa using this
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hlt⟩
  have hνL : ν Lᶜ = 0 := by
    rw [hν, withDensity_apply _ hL.isClosed.measurableSet.compl]
    have : ∀ y ∈ Lᶜ, (p y : ENNReal) = 0 := fun y hy => by simp [hpL y hy]
    rw [setLIntegral_congr_fun hL.isClosed.measurableSet.compl this]
    simp
  have key := GlobalTheory.T.isSmoothFun_integral_mul_right' 𝔸 G 𝔤 h ν L hL hνL κ hκ
  convert key using 2 with z
  rw [hν, integral_withDensity_eq_integral_smul hp]
  congr 1
  funext y
  rw [NNReal.smul_def, Complex.real_smul, mul_comm]

end GlobalTheory.ConvSmooth

namespace GlobalTheory.ConvSmooth

theorem posPart_decomp (w : ℂ) :
    w = (((Real.toNNReal w.re : NNReal) : ℝ) : ℂ) - (((Real.toNNReal (-w.re) : NNReal) : ℝ) : ℂ) +
      Complex.I * ((((Real.toNNReal w.im : NNReal) : ℝ) : ℂ) -
        (((Real.toNNReal (-w.im) : NNReal) : ℝ) : ℂ)) := by
  apply Complex.ext <;> simp [Real.coe_toNNReal', max_zero_sub_max_neg_zero_eq_self]

theorem conv_smooth_compactSupport : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Set G, IsCompact K → ∀ κ a : G → ℂ, h.IsSmoothFun κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → h.IsSmoothFun (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) ∧ HasCompactSupport (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) := by
  intro 𝔸 _ _ _ _ G 𝔤 h _ _ μ hμ K hK κ a hκ hκc ha hai haK
  haveI := h.locallyCompactSpace
  haveI := secondCountable_units 𝔸
  haveI : SecondCountableTopology G := Topology.IsInducing.subtypeVal.secondCountableTopology
  constructor
  · set b : G → ℂ := fun y => a y⁻¹ with hb
    have hbm : Measurable b := ha.comp measurable_inv
    have hbK : ∀ y ∉ K⁻¹, b y = 0 := fun y hy => haK _ (by simpa [Set.mem_inv] using hy)
    have hbi : Integrable b μ := by
      obtain ⟨B, hB⟩ := GlobalTheory.T.lintegral_inv_le_of_support_compact_alt G μ hμ K hK
      refine ⟨hbm.aestronglyMeasurable, ?_⟩
      have h1 := hB (fun x => ‖a x‖ₑ) ha.enorm (fun x hx => by simp [haK x hx])
      exact lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.coe_lt_top hai.2)
    have hcv : ∀ z, ∫ x, κ x * a (x⁻¹ * z) ∂μ = ∫ y, κ (z * y) * b y ∂μ := by
      intro z
      rw [← integral_mul_left_eq_self (fun x => κ x * a (x⁻¹ * z)) z]
      congr 1; funext y; simp [hb, mul_inv_rev, mul_assoc]
    have hκcont : Continuous κ := by
      letI := h.chartedSpace
      exact ContMDiff.continuous hκ
    obtain ⟨C, hC⟩ := hκcont.bounded_above_of_compact_support hκc
    have hre : Integrable (fun y => (b y).re) μ := by simpa using hbi.re
    have him : Integrable (fun y => (b y).im) μ := by simpa using hbi.im
    have hpos : ∀ f : G → ℝ, Integrable f μ → Integrable (fun y => ((Real.toNNReal (f y) : NNReal) : ℝ)) μ :=
      fun f hf => by simpa [Real.coe_toNNReal'] using hf.pos_part
    have hK' : IsCompact K⁻¹ := hK.inv
    have hre' : Integrable (fun y => -(b y).re) μ := hre.neg
    have him' : Integrable (fun y => -(b y).im) μ := him.neg
    have S : ∀ f : G → ℝ, Measurable f → Integrable f μ → (∀ y ∉ K⁻¹, f y = 0) →
        h.IsSmoothFun (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (f y) : NNReal) : ℝ) : ℂ) ∂μ) :=
      fun f hfm hf hf0 => isSmoothFun_density h μ hK' hκ hfm.real_toNNReal (hpos f hf)
        (fun y hy => by simp [hf0 y hy])
    have hbre : ∀ y ∉ K⁻¹, (b y).re = 0 := fun y hy => by simp [hbK y hy]
    have hbim : ∀ y ∉ K⁻¹, (b y).im = 0 := fun y hy => by simp [hbK y hy]
    have s1 := S _ (Complex.measurable_re.comp hbm) hre hbre
    have s2 := S _ (Complex.measurable_re.comp hbm).neg hre' (fun y hy => by simp [hbre y hy])
    have s3 := S _ (Complex.measurable_im.comp hbm) him hbim
    have s4 := S _ (Complex.measurable_im.comp hbm).neg him' (fun y hy => by simp [hbim y hy])
    have hI : ∀ (z : G) (f : G → ℝ), Integrable f μ →
        Integrable (fun y => κ (z * y) * (((Real.toNNReal (f y) : NNReal) : ℝ) : ℂ)) μ := by
      intro z f hf
      refine ((hpos f hf).ofReal (𝕜 := ℂ)).bdd_mul (hκcont.comp (continuous_const_mul z)).aestronglyMeasurable (ae_of_all _ fun y => hC _)
    have hsum : (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) =
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (b y).re : NNReal) : ℝ) : ℂ) ∂μ) -
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (-(b y).re) : NNReal) : ℝ) : ℂ) ∂μ) +
        Complex.I • ((fun z => ∫ y, κ (z * y) * (((Real.toNNReal (b y).im : NNReal) : ℝ) : ℂ) ∂μ) -
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (-(b y).im) : NNReal) : ℝ) : ℂ) ∂μ)) := by
      funext z
      rw [hcv z]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e : (fun y => κ (z * y) * b y) = fun y =>
          (κ (z * y) * (((Real.toNNReal (b y).re : NNReal) : ℝ) : ℂ) -
            κ (z * y) * (((Real.toNNReal (-(b y).re) : NNReal) : ℝ) : ℂ)) +
          Complex.I * (κ (z * y) * (((Real.toNNReal (b y).im : NNReal) : ℝ) : ℂ) -
            κ (z * y) * (((Real.toNNReal (-(b y).im) : NNReal) : ℝ) : ℂ)) := by
        funext y
        conv_lhs => rw [posPart_decomp (b y)]
        ring
      rw [e, integral_add ?_ ?_, integral_sub ?_ ?_, integral_const_mul, integral_sub ?_ ?_]
      all_goals first
        | exact hI z _ hre | exact hI z _ hre' | exact hI z _ him | exact hI z _ him'
        | exact (hI z _ hre).sub (hI z _ hre')
        | exact ((hI z _ him).sub (hI z _ him')).const_mul _
    rw [← h.mem_smoothFuns, hsum]
    exact Submodule.add_mem _ (Submodule.sub_mem _ s1 s2)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ s3 s4))
  · refine HasCompactSupport.intro (hκc.mul hK) fun z hz => ?_
    have : (fun x => κ x * a (x⁻¹ * z)) = 0 := by
      funext x
      by_cases hx : x ∈ tsupport κ
      · have : x⁻¹ * z ∉ K := fun h' => hz ⟨x, hx, x⁻¹ * z, h', by simp⟩
        simp [haK _ this]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    simp only [this]; exact integral_zero' ..

end GlobalTheory.ConvSmooth
