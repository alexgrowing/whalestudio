import Mathlib
import GroundTheory.AutomorphicForms.QuotientKernel
import GroundTheory.AutomorphicForms.KernelTraceComp
import GroundTheory.AutomorphicForms.LocallyConstantCompact

open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

section Convolution

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)

def convFun (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) (x : G) : ℂ :=
  ∫ g, f₁ g * f₂ (g⁻¹ * x) ∂μ

theorem convFun_eq_setIntegral (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) (x : G) :
    convFun μ f₁ f₂ x = ∫ g in tsupport f₁, f₁ g * f₂ (g⁻¹ * x) ∂μ := by
  rw [convFun, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro g hg
  rw [image_eq_zero_of_notMem_tsupport hg, zero_mul]

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] [IsFiniteMeasureOnCompacts μ] in
theorem continuous_convFun (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    Continuous (convFun μ f₁ f₂) := by
  have h : convFun μ f₁ f₂ = fun x => ∫ g in tsupport f₁, f₁ g * f₂ (g⁻¹ * x) ∂μ :=
    funext (convFun_eq_setIntegral μ f₁ f₂)
  rw [h]
  exact continuous_parametric_integral_of_continuous (f := fun x g => f₁ g * f₂ (g⁻¹ * x))
    (by fun_prop) f₁.hasCompactSupport

theorem convFun_eq_zero (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) {x : G}
    (hx : x ∉ tsupport f₁ * tsupport f₂) : convFun μ f₁ f₂ x = 0 := by
  rw [convFun]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun g => ?_)
  by_cases h1 : g ∈ tsupport f₁
  · have h2 : g⁻¹ * x ∉ tsupport f₂ := fun h2 =>
      hx ⟨g, h1, g⁻¹ * x, h2, by simp only [mul_inv_cancel_left]⟩
    simp [image_eq_zero_of_notMem_tsupport h2]
  · simp [image_eq_zero_of_notMem_tsupport h1]

variable [IsTopologicalGroup G] [T2Space G] in
theorem hasCompactSupport_convFun (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    HasCompactSupport (convFun μ f₁ f₂) :=
  HasCompactSupport.intro (f₁.hasCompactSupport.mul f₂.hasCompactSupport)
    fun _ hx => convFun_eq_zero μ f₁ f₂ hx

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
  [BorelSpace G] [IsFiniteMeasureOnCompacts μ]

def conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) : CompactlySupportedContinuousMap G ℂ where
  toFun := convFun μ f₁ f₂
  continuous_toFun := continuous_convFun μ f₁ f₂
  hasCompactSupport' := hasCompactSupport_convFun μ f₁ f₂

theorem conv_apply (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) (x : G) :
    conv μ f₁ f₂ x = ∫ g, f₁ g * f₂ (g⁻¹ * x) ∂μ :=
  rfl

end Convolution

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in

theorem finite_setOf_mem_of_isCompact [IsTopologicalGroup G] {C : Set G} (hC : IsCompact C) :
    {δ : Γ | (δ : G) ∈ C}.Finite := by
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  exact (hcl.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage hC).finite_of_discrete

section Kernel

variable (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]

theorem quotientKernel_conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ)
    (x z : RightCosetSpace Γ) :
    quotientKernel Γ (conv μ f₁ f₂) (x, z) =
      ∫ y, quotientKernel Γ f₁ (x, y) * quotientKernel Γ f₂ (y, z) ∂quotientMeasure Γ μ := by
  obtain ⟨a, rfl⟩ := mk_surjective Γ x
  obtain ⟨b, rfl⟩ := mk_surjective Γ z
  let φ : C(RightCosetSpace Γ, ℂ) :=
    ⟨fun y => quotientKernel Γ f₂ (y, mk Γ b),
      (continuous_quotientKernel Γ f₂).comp (continuous_id.prodMk continuous_const)⟩
  have hφ := integral_mul_rightMul_eq Γ μ f₁ φ (mk Γ a)
  simp only [φ, ContinuousMap.coe_mk] at hφ
  rw [← hφ]

  set C : Set G := a • ((tsupport f₁ * tsupport f₂) * {b⁻¹}) with hC
  have hCc : IsCompact C :=
    ((f₁.hasCompactSupport.mul f₂.hasCompactSupport).mul isCompact_singleton).smul a
  have hfin := finite_setOf_mem_of_isCompact Γ hCc
  set S := hfin.toFinset
  have hmem : ∀ δ : Γ, (∃ g, f₁ g * f₂ (g⁻¹ * (a⁻¹ * δ * b)) ≠ 0) → δ ∈ S := by
    rintro δ ⟨g, hg⟩
    rw [Finite.mem_toFinset]
    have h1 : g ∈ tsupport f₁ := subset_tsupport _ (left_ne_zero_of_mul hg)
    have h2 : g⁻¹ * (a⁻¹ * δ * b) ∈ tsupport f₂ := subset_tsupport _ (right_ne_zero_of_mul hg)
    refine ⟨(a⁻¹ * δ * b) * b⁻¹, ⟨a⁻¹ * δ * b, ⟨g, h1, _, h2, by group⟩, b⁻¹, rfl, rfl⟩, ?_⟩
    simp only [smul_eq_mul]
    group
  have hsupp' : (support fun δ : Γ => conv μ f₁ f₂ (a⁻¹ * δ * b)) ⊆ S := by
    intro δ hδ
    rw [mem_support, conv_apply] at hδ
    by_contra hS
    exact hδ (integral_eq_zero_of_ae (Eventually.of_forall fun g => by
      by_contra h
      exact hS (hmem δ ⟨g, h⟩)))
  have hint : ∀ δ : Γ, Integrable (fun g => f₁ g * f₂ (g⁻¹ * (a⁻¹ * δ * b))) μ := fun δ =>
    (by fun_prop : Continuous fun g => f₁ g * f₂ (g⁻¹ * (a⁻¹ * δ * b))).integrable_of_hasCompactSupport
      f₁.hasCompactSupport.mul_right
  rw [quotientKernel_mk, finsum_eq_sum_of_support_subset _ hsupp']
  simp only [conv_apply]
  rw [← integral_finsetSum _ fun δ _ => hint δ]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [rightMul_mk, quotientKernel_mk]
  by_cases hg : f₁ g = 0
  · simp [hg]
  rw [finsum_eq_sum_of_support_subset _ (s := S) ?_, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun δ _ => ?_
    congr 2
    group
  · intro δ hδ
    refine hmem δ ⟨g, mul_ne_zero hg ?_⟩
    rw [mem_support] at hδ
    have : g⁻¹ * (a⁻¹ * δ * b) = (a * g)⁻¹ * δ * b := by group
    rwa [this]

def quotientKernelC (f : CompactlySupportedContinuousMap G ℂ) :
    C(RightCosetSpace Γ × RightCosetSpace Γ, ℂ) :=
  ⟨quotientKernel Γ f, continuous_quotientKernel Γ f⟩

@[simp] theorem quotientKernelC_apply (f : CompactlySupportedContinuousMap G ℂ)
    (p : RightCosetSpace Γ × RightCosetSpace Γ) : quotientKernelC Γ f p = quotientKernel Γ f p :=
  rfl

variable [CompactSpace (RightCosetSpace Γ)]

theorem quotientKernelC_conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    quotientKernelC Γ (conv μ f₁ f₂) =
      compKernel (quotientMeasure Γ μ) (quotientKernelC Γ f₁) (quotientKernelC Γ f₂) := by
  ext ⟨x, z⟩
  rw [compKernel_apply, quotientKernelC_apply, quotientKernel_conv Γ μ f₁ f₂ x z]
  rfl

end Kernel

section Operator

variable (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]
  [CompactSpace (RightCosetSpace Γ)]

theorem kernelOperator_eq_contKernelOp (f : CompactlySupportedContinuousMap G ℂ) :
    kernelOperator Γ μ f = contKernelOp (quotientMeasure Γ μ) (quotientKernelC Γ f) :=
  rfl

theorem integrated_conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    (rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ (conv μ f₁ f₂)) =
      ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f₁)).comp
        ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f₂)) := by
  rw [integrated_rightRegularRep_eq_kernelOperator, integrated_rightRegularRep_eq_kernelOperator,
    integrated_rightRegularRep_eq_kernelOperator, kernelOperator_eq_contKernelOp,
    kernelOperator_eq_contKernelOp, kernelOperator_eq_contKernelOp, quotientKernelC_conv,
    contKernelOp_comp]

theorem isTraceClass_integrated_conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    IsTraceClass ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ (conv μ f₁ f₂))) := by
  rw [integrated_conv]
  exact isTraceClass_comp (isHilbertSchmidt_integrated_rightRegularRep Γ μ f₁)
    (isHilbertSchmidt_integrated_rightRegularRep Γ μ f₂)

end Operator

end RightCosetSpace

section TotallyDisconnected

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def indicatorOne (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    CompactlySupportedContinuousMap G ℂ where
  toFun := (K : Set G).indicator 1
  continuous_toFun := by
    rw [← LocallyConstant.coe_charFn ℂ K.isClopen]
    exact (LocallyConstant.charFn ℂ K.isClopen).continuous
  hasCompactSupport' := HasCompactSupport.intro hK fun _ hx => indicator_of_notMem hx _

theorem indicatorOne_apply (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    indicatorOne K hK x = (K : Set G).indicator 1 x :=
  rfl

variable (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]

theorem conv_indicatorOne (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : CompactlySupportedContinuousMap G ℂ) (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) (x : G) :
    conv μ f (indicatorOne K hK) x = (μ.real (K : Set G) : ℂ) * f x := by
  rw [conv_apply]
  have h : (fun g => f g * indicatorOne K hK (g⁻¹ * x)) =
      (x • (K : Set G)).indicator (fun _ => f x) := by
    funext g
    by_cases hg : g ∈ x • (K : Set G)
    · obtain ⟨k, hk, rfl⟩ := mem_smul_set.1 hg
      have hk' : (x • k)⁻¹ * x ∈ (K : Set G) := by
        rw [smul_eq_mul, mul_inv_rev, inv_mul_cancel_right]
        exact inv_mem hk
      rw [indicatorOne_apply, indicator_of_mem hk', indicator_of_mem hg, smul_eq_mul, hf x k hk,
        Pi.one_apply, mul_one]
    · have hx : g⁻¹ * x ∉ (K : Set G) := fun h => hg (mem_smul_set.2
        ⟨(g⁻¹ * x)⁻¹, inv_mem h, by rw [smul_eq_mul, mul_inv_rev, inv_inv, mul_inv_cancel_left]⟩)
      rw [indicatorOne_apply, indicator_of_notMem hx, indicator_of_notMem hg, mul_zero]
  rw [h, integral_indicator_const _ ((K.isOpen.smul x).measurableSet)]
  have hvol : μ.real (x • (K : Set G)) = μ.real (K : Set G) := by
    simp [Measure.real, measure_smul]
  rw [hvol, Complex.real_smul]

variable [TotallyDisconnectedSpace G]

theorem exists_eq_conv_of_isLocallyConstant [μ.IsOpenPosMeasure]
    (f : CompactlySupportedContinuousMap G ℂ) (hf : IsLocallyConstant (f : G → ℂ)) :
    ∃ f₁ f₂ : CompactlySupportedContinuousMap G ℂ, f = conv μ f₁ f₂ := by
  have hmem : (f : G → ℂ) ∈ locallyConstantCompactSupport G ℂ ℂ := ⟨hf, f.hasCompactSupport⟩
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_right hmem
  have hpos : 0 < μ.real (K : Set G) :=
    ENNReal.toReal_pos (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne' hKc.measure_lt_top.ne
  set c : ℂ := (((μ.real (K : Set G))⁻¹ : ℝ) : ℂ)
  refine ⟨c • f, indicatorOne K hKc, ?_⟩
  ext x
  rw [conv_indicatorOne μ K hKc (c • f) (fun g k hk => by
    simp only [CompactlySupportedContinuousMap.smul_apply, hK g k hk]) x]
  simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, c]
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]

end TotallyDisconnected

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [TotallyDisconnectedSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem isTraceClass_integrated_of_isLocallyConstant (f : CompactlySupportedContinuousMap G ℂ)
    (hf : IsLocallyConstant (f : G → ℂ)) :
    IsTraceClass ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)) := by
  obtain ⟨f₁, f₂, rfl⟩ := exists_eq_conv_of_isLocallyConstant μ f hf
  exact isTraceClass_integrated_conv Γ μ f₁ f₂

end RightCosetSpace

end

end GroundTheory.Automorphic
