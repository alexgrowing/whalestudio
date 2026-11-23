import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.CuspidalProjection.Unfold
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import GroundTheory.AutomorphicForms.CuspidalProjection.ContinuousFiniteAdeleSingleAdd
import GroundTheory.AutomorphicForms.RealIwasawaIntegration

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise InnerProductSpace ComplexConjugate NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalProjection

open Reduction AutomorphicForm CuspidalSpectrum RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem integral_rconv_unip_eq (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (r : ℕ) (x : normOneGL K n) :
    ∫ X in unipFundamentalDomain K n r, rconv Γ₁ μ f φ (unipOne K n r X * x)
      ∂unipMeasure K n r = ∫ z, f (x⁻¹ * z) * constantTermL2 μ r φ z ∂μ := by
  set S := (x * ·) '' tsupport (f : normOneGL K n → ℂ)
  have hS : IsCompact S := f.hasCompactSupport.isCompact.image (continuous_const_mul x)
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hfS : ∀ z ∉ S, f (x⁻¹ * z) = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz ⟨x⁻¹ * z, h, by simp⟩
  set F : (UPos n r → 𝔸[K]) → normOneGL K n → ℂ :=
    fun X z => f (x⁻¹ * z) * φ (mk Γ₁ (unipOne K n r X * z))
  have hFm : StronglyMeasurable (uncurry F) :=
    (f.continuous.comp (continuous_const_mul x⁻¹ |>.comp continuous_snd)).stronglyMeasurable.mul
      ((Lp.stronglyMeasurable φ).comp_measurable ((measurable_mk Γ₁).comp
        (continuous_unipOne_mul r).measurable))
  have hint : Integrable (uncurry F)
      (((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC, hCφ⟩ := exists_lintegral_unip_sq_le μ r hS
    have hfin : ∫⁻ z in S, ∫⁻ X in unipFundamentalDomain K n r,
        ‖φ (mk Γ₁ (unipOne K n r X * z))‖ₑ ∂unipMeasure K n r ∂μ < ⊤ :=
      L2Kernel.lt_top_of_sq_lt_top ((hCφ φ).trans_lt
        (ENNReal.mul_lt_top hC.lt_top (ENNReal.pow_lt_top enorm_lt_top)))
    have hmeas : Measurable fun p : (UPos n r → 𝔸[K]) × normOneGL K n =>
        ‖φ (mk Γ₁ (unipOne K n r p.1 * p.2))‖ₑ :=
      ((Lp.stronglyMeasurable φ).measurable.comp ((measurable_mk Γ₁).comp
        (continuous_unipOne_mul r).measurable)).enorm
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFm.aestronglyMeasurable.enorm]
    calc ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ z, ‖uncurry F (X, z)‖ₑ ∂μ ∂unipMeasure K n r
        ≤ ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ z in S,
            ENNReal.ofReal M * ‖φ (mk Γ₁ (unipOne K n r X * z))‖ₑ ∂μ ∂unipMeasure K n r := by
          refine lintegral_mono fun X => ?_
          rw [← lintegral_indicator hS.measurableSet]
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ S
          · rw [indicator_of_mem hz]
            simp only [F, uncurry_apply_pair, enorm_mul]
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hM _)
          · rw [indicator_of_notMem hz]
            simp [F, hfS z hz]
      _ = ENNReal.ofReal M * ∫⁻ z in S, ∫⁻ X in unipFundamentalDomain K n r,
            ‖φ (mk Γ₁ (unipOne K n r X * z))‖ₑ ∂unipMeasure K n r ∂μ := by
          simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_lintegral_swap hmeas.aemeasurable
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hinner : ∀ X, rconv Γ₁ μ f φ (unipOne K n r X * x) = ∫ z, F X z ∂μ := by
    intro X
    rw [rconv, ← integral_mul_left_eq_self _ (unipOne K n r X)]
    congr 1
    ext z
    simp only [F, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hCT : ∀ z, ∫ X in unipFundamentalDomain K n r, F X z ∂unipMeasure K n r =
      f (x⁻¹ * z) * constantTermL2 μ r φ z := by
    intro z
    simp only [F, constantTermL2, ctFun]
    exact integral_const_mul _ _
  simp_rw [hinner]
  rw [integral_integral_swap hint]
  simp_rw [hCT]

theorem constantTermL2_unipotent_mul (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (r : ℕ)
    (Y : UPos n r → 𝔸[K]) (z : normOneGL K n) :
    constantTermL2 μ r φ (unipOne K n r Y * z) = constantTermL2 μ r φ z := by
  simp only [constantTermL2, ctFun]
  have h : ∀ X, unipOne K n r X * (unipOne K n r Y * z) = unipOne K n r (X + Y) * z := by
    intro X
    rw [unipOne_add, mul_assoc]
  simp_rw [h]
  refine setIntegral_add_right_of_periodic isAddFundamentalDomain_unipFundamentalDomain
    (h := fun X => (φ : RightCosetSpace Γ₁ → ℂ) (mk Γ₁ (unipOne K n r X * z))) (fun ξ hξ s => ?_) Y
  show (φ : RightCosetSpace Γ₁ → ℂ) (mk Γ₁ (unipOne K n r (ξ + s) * z)) = φ (mk Γ₁ (unipOne K n r s * z))
  rw [unipOne_add, mul_assoc, mk_mul_of_mem (unipOne_mem_rationalGLOne r ⟨ξ, hξ⟩)]

theorem integrableOn_constantTermL2 (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (r : ℕ)
    {S : Set (normOneGL K n)} (hS : IsCompact S) : IntegrableOn (constantTermL2 μ r φ) S μ := by
  obtain ⟨C, hC, hCφ⟩ := exists_lintegral_constantTermL2_sq_le μ r hS
  refine ⟨(stronglyMeasurable_ctFun r (Lp.stronglyMeasurable φ)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact L2Kernel.lt_top_of_sq_lt_top ((hCφ φ).trans_lt
    (ENNReal.mul_lt_top hC.lt_top (ENNReal.pow_lt_top enorm_lt_top)))

variable (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
  [BorelSpace (v.adicCompletion K)]

def IsCuspidalAt (ν : ∀ r : ℕ, Measure (UPos n r → v.adicCompletion K)) (f : normOneGL K n → ℂ) :
    Prop :=
  ∀ r : ℕ, 0 < r → r < n → ∀ g₁ g₂ : normOneGL K n,
    ∫ y, f (g₁ * unipAt n r v y * g₂) ∂ν r = 0

variable {μ v}

theorem integrated_mem_cuspidalL2 {ν : ∀ r : ℕ, Measure (UPos n r → v.adicCompletion K)}
    [∀ r, (ν r).IsAddHaarMeasure] {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    (hf : IsCuspidalAt v ν f) (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) φ ∈ cuspidalL2 μ := by
  intro r hr hrn
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  filter_upwards [ae_ctFun_congr μ r (integrated_ae_eq_rconvQ Γ₁ μ f φ)] with y hy
  rw [constantTermL2, hy, Pi.zero_apply]
  simp only [ctFun, rconvQ_mk]
  rw [integral_rconv_unip_eq]
  have hhc : HasCompactSupport fun z : normOneGL K n => f (y⁻¹ * z) :=
    f.hasCompactSupport.comp_isClosedEmbedding (Homeomorph.mulLeft y⁻¹).isClosedEmbedding
  exact integral_mul_eq_zero_of_integral_eq_zero (ν := ν r) (isProperHom_unipAt v)
    (h := fun z => f (y⁻¹ * z)) (f.continuous.comp (continuous_const_mul _)) hhc
    (stronglyMeasurable_ctFun r (Lp.stronglyMeasurable φ)).aestronglyMeasurable
    (integrableOn_constantTermL2 μ φ r hhc.isCompact)
    (fun b z => constantTermL2_unipotent_mul μ φ r _ z)
    (fun z => by simpa only [mul_assoc] using hf r hr hrn y⁻¹ z)

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem unipAt_neg (r : ℕ) (y : UPos n r → v.adicCompletion K) :
    unipAt n r v (-y) = (unipAt n r v y)⁻¹ := by
  have h0 : unipAt n r v (0 : UPos n r → v.adicCompletion K) = 1 := by
    rw [unipAt]
    simp only [Pi.zero_apply, map_zero]
    exact unipOne_zero r
  rw [eq_inv_iff_mul_eq_one, ← unipAt_add, neg_add_cancel, h0]

def ccStar (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    CompactlySupportedContinuousMap (normOneGL K n) ℂ where
  toFun g := conj (f g⁻¹)
  continuous_toFun := Complex.continuous_conj.comp (f.continuous.comp continuous_inv)
  hasCompactSupport' :=
    (f.hasCompactSupport.comp_isClosedEmbedding (Homeomorph.inv (normOneGL K n)).isClosedEmbedding).comp_left
      (map_zero _)

@[simp] theorem ccStar_apply (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (g : normOneGL K n) : ccStar f g = conj (f g⁻¹) := rfl

theorem isCuspidalAt_ccStar {ν : ∀ r : ℕ, Measure (UPos n r → v.adicCompletion K)}
    [∀ r, (ν r).IsAddHaarMeasure] {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    (hf : IsCuspidalAt v ν f) : IsCuspidalAt v ν (ccStar f) := by
  intro r hr hrn g₁ g₂
  have h : ∀ y, ccStar f (g₁ * unipAt n r v y * g₂) = conj (f (g₂⁻¹ * unipAt n r v (-y) * g₁⁻¹)) := by
    intro y
    rw [ccStar_apply, unipAt_neg]
    congr 2
    group
  simp_rw [h]
  have : (ν r).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  rw [integral_conj, integral_neg_eq_self (fun y => f (g₂⁻¹ * unipAt n r v y * g₁⁻¹)),
    hf r hr hrn, map_zero]

variable (μ) in

theorem ccToL1_ccStar [μ.IsInvInvariant] (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    UnitaryRep.ccToL1 μ (ccStar f) = UnitaryRep.involution μ (UnitaryRep.ccToL1 μ f) := by
  have h1 : (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) =ᵐ[μ] f :=
    MemLp.coeFn_toLp _
  have h1' : (fun g => (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) g⁻¹) =ᵐ[μ] fun g => f g⁻¹ :=
    (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae_eq_comp h1
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (μ := μ) ((ccStar f).continuous.memLp_of_hasCompactSupport
    (ccStar f).hasCompactSupport), UnitaryRep.coeFn_involution μ (UnitaryRep.ccToL1 μ f), h1']
    with g ha hb hc
  rw [hb, hc]
  exact ha

theorem integrated_eq_zero_of_mem_orthogonal {ν : ∀ r : ℕ, Measure (UPos n r → v.adicCompletion K)}
    [∀ r, (ν r).IsAddHaarMeasure] {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    (hf : IsCuspidalAt v ν f) {ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} (hψ : ψ ∈ (cuspidalL2 μ)ᗮ) :
    (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ψ = 0 := by
  have := isInvInvariant_of_isMulRightInvariant μ
  have hadj : ContinuousLinearMap.adjoint
      ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f)) =
      (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ (ccStar f)) := by
    exact ((rightRegularRep Γ₁ μ).adjoint_integrated μ (UnitaryRep.ccToL1 μ f)).trans
      (congrArg _ (ccToL1_ccStar μ f).symm)
  refine ext_inner_left ℂ fun w => ?_
  have h1 := (ContinuousLinearMap.adjoint_inner_left
    ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f)) ψ w).symm
  have h2 := (Submodule.mem_orthogonal _ _).1 hψ _
    (integrated_mem_cuspidalL2 (isCuspidalAt_ccStar hf) w)
  rw [← hadj] at h2
  exact h1.trans (h2.trans (inner_zero_right _).symm)

theorem starProjection_comp_integrated {ν : ∀ r : ℕ, Measure (UPos n r → v.adicCompletion K)}
    [∀ r, (ν r).IsAddHaarMeasure] {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    (hf : IsCuspidalAt v ν f) :
    (cuspidalL2 μ).starProjection ∘L (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) =
      (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) :=
  ContinuousLinearMap.ext fun φ =>
    Submodule.starProjection_eq_self_iff.2 (integrated_mem_cuspidalL2 hf φ)

theorem integrated_comp_starProjection {ν : ∀ r : ℕ, Measure (UPos n r → v.adicCompletion K)}
    [∀ r, (ν r).IsAddHaarMeasure] {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    (hf : IsCuspidalAt v ν f) :
    (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L (cuspidalL2 μ).starProjection =
      (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) := by
  refine ContinuousLinearMap.ext fun φ => ?_
  have h : φ - (cuspidalL2 μ).starProjection φ ∈ (cuspidalL2 μ)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal φ
  have h0 := integrated_eq_zero_of_mem_orthogonal hf h
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm

end CuspidalProjection

end

end GroundTheory.Automorphic
