import Mathlib
import GroundTheory.AutomorphicForms.QuotientRightRegular
import GroundTheory.AutomorphicForms.HilbertSchmidtKernel
import GroundTheory.AutomorphicForms.HilbertSchmidtCompact
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract

open MeasureTheory Topology Filter Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G)

def automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) (p : G × G) : ℂ :=
  ∑ᶠ γ : Γ, f (p.1⁻¹ * γ * p.2)

theorem automorphicKernel_smul_left (f : CompactlySupportedContinuousMap G ℂ) (δ : Γ) (a b : G) :
    automorphicKernel Γ f (δ • a, b) = automorphicKernel Γ f (a, b) := by
  unfold automorphicKernel
  rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]
  congr 1
  group

theorem automorphicKernel_smul_right (f : CompactlySupportedContinuousMap G ℂ) (δ : Γ) (a b : G) :
    automorphicKernel Γ f (a, δ • b) = automorphicKernel Γ f (a, b) := by
  unfold automorphicKernel
  rw [← finsum_comp_equiv (Equiv.mulRight δ⁻¹)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulRight, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  congr 1
  group

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ]

theorem locallyFinite_support_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) :
    LocallyFinite fun γ : Γ => support fun p : G × G => f (p.1⁻¹ * γ * p.2) := by
  intro p
  obtain ⟨A, hAc, hA⟩ := exists_compact_mem_nhds p.1
  obtain ⟨B, hBc, hB⟩ := exists_compact_mem_nhds p.2
  refine ⟨A ×ˢ B, prod_mem_nhds hA hB, ?_⟩
  have hAS : IsCompact (A * tsupport f) := hAc.mul f.hasCompactSupport
  refine (ProperlyDiscontinuousSMul.finite_disjoint_inter_image hBc hAS).subset ?_
  rintro γ ⟨⟨a, b⟩, hq, hab⟩
  simp only [mem_prod] at hab
  refine ⟨γ • b, mem_image_of_mem _ hab.2, ?_⟩
  refine ⟨a, hab.1, a⁻¹ * γ * b, subset_tsupport _ hq, ?_⟩
  rw [Subgroup.smul_def, smul_eq_mul]
  group

theorem continuous_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) :
    Continuous (automorphicKernel Γ f) :=
  continuous_finsum (fun γ => f.continuous.comp (by fun_prop))
    (locallyFinite_support_automorphicKernel Γ f)

theorem finite_support_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) (p : G × G) :
    (support fun γ : Γ => f (p.1⁻¹ * γ * p.2)).Finite := by
  exact (locallyFinite_support_automorphicKernel Γ f).point_finite p

def quotientKernel (f : CompactlySupportedContinuousMap G ℂ)
    (p : RightCosetSpace Γ × RightCosetSpace Γ) : ℂ :=
  Quotient.lift₂ (fun a b => automorphicKernel Γ f (a, b)) (fun a₁ b₁ a₂ b₂ ha hb => by
    obtain ⟨δ, rfl⟩ := ha
    obtain ⟨ε, rfl⟩ := hb
    rw [automorphicKernel_smul_left, automorphicKernel_smul_right]) p.1 p.2

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ] in
@[simp] theorem quotientKernel_mk (f : CompactlySupportedContinuousMap G ℂ) (a b : G) :
    quotientKernel Γ f (mk Γ a, mk Γ b) = ∑ᶠ γ : Γ, f (a⁻¹ * γ * b) :=
  rfl

theorem continuous_quotientKernel (f : CompactlySupportedContinuousMap G ℂ) :
    Continuous (quotientKernel Γ f) := by
  have hq : IsQuotientMap (Prod.map (mk Γ) (mk Γ)) :=
    ((isOpenQuotientMap_mk Γ).prodMap (isOpenQuotientMap_mk Γ)).isQuotientMap
  refine hq.continuous_iff.2 ?_
  exact continuous_automorphicKernel Γ f

section Operator

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]

def rightRegularRep : UnitaryRep G (Lp ℂ 2 (quotientMeasure Γ μ)) :=
  UnitaryRep.ofLinearIsometryEquiv (rightRegular Γ μ) (continuous_rightRegular_apply Γ μ)

theorem rightRegularRep_apply (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightRegularRep Γ μ g φ = rightTranslate Γ μ g φ :=
  rfl

theorem coeFn_rightRegularRep (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightRegularRep Γ μ g φ =ᵐ[quotientMeasure Γ μ] fun x => φ (rightMul Γ g x) :=
  coeFn_rightTranslate Γ μ g φ

omit [μ.IsMulRightInvariant] in

theorem integral_mul_rightMul_eq (f : CompactlySupportedContinuousMap G ℂ)
    (φ : C(RightCosetSpace Γ, ℂ)) (x : RightCosetSpace Γ) :
    ∫ g, f g * φ (rightMul Γ g x) ∂μ =
      ∫ y, quotientKernel Γ f (x, y) * φ y ∂quotientMeasure Γ μ := by
  obtain ⟨a, rfl⟩ := mk_surjective Γ x
  have h1 : ∫ g, f g * φ (rightMul Γ g (mk Γ a)) ∂μ = ∫ g, φ (mk Γ g) * f (a⁻¹ * g) ∂μ := by
    rw [← integral_mul_left_eq_self (fun g => φ (mk Γ g) * f (a⁻¹ * g)) a]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [rightMul_mk, inv_mul_cancel_left, mul_comm]
  have hcs : HasCompactSupport fun g => f (a⁻¹ * g) :=
    f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft a⁻¹)
  have hint : Integrable (fun g => φ (mk Γ g) * f (a⁻¹ * g)) μ :=
    ((φ.continuous.comp (continuous_mk Γ)).mul
      (f.continuous.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hcs.mul_left
  rw [h1, integral_mul_eq_integral_mul_automorphize μ hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  obtain ⟨b, rfl⟩ := mk_surjective Γ y
  dsimp only
  rw [quotientKernel_mk, mul_comm]
  congr 1
  change ∑' γ : Γ, f (a⁻¹ * (γ • b)) = _
  simp_rw [Subgroup.smul_def, smul_eq_mul, ← mul_assoc]
  exact tsum_eq_finsum (finite_support_automorphicKernel Γ f (a, b))

variable [CompactSpace (RightCosetSpace Γ)]

omit [μ.IsMulRightInvariant] in

theorem memLp_quotientKernel (f : CompactlySupportedContinuousMap G ℂ) :
    MemLp (quotientKernel Γ f) 2 ((quotientMeasure Γ μ).prod (quotientMeasure Γ μ)) :=
  (continuous_quotientKernel Γ f).memLp_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

omit [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in
theorem coeFn_compactSupportToL1 (f : CompactlySupportedContinuousMap G ℂ) :
    (UnitaryRep.ccToL1 μ f : G → ℂ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp _

def kernelOperator (f : CompactlySupportedContinuousMap G ℂ) :
    Lp ℂ 2 (quotientMeasure Γ μ) →L[ℂ] Lp ℂ 2 (quotientMeasure Γ μ) :=
  L2Kernel.kernelOp ((memLp_quotientKernel Γ μ f).toLp _)

omit [μ.IsMulRightInvariant] in

theorem isHilbertSchmidt_kernelOperator (f : CompactlySupportedContinuousMap G ℂ) :
    IsHilbertSchmidt (kernelOperator Γ μ f) :=
  L2Kernel.kernelOp_isHilbertSchmidt _

theorem inner_integrated_toLp (f : CompactlySupportedContinuousMap G ℂ)
    (φ ψ : C(RightCosetSpace Γ, ℂ)) :
    ⟪ContinuousMap.toLp 2 (quotientMeasure Γ μ) ℂ ψ,
      (rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)
        (ContinuousMap.toLp 2 (quotientMeasure Γ μ) ℂ φ)⟫_ℂ =
      ∫ x, conj (ψ x) * ∫ y, quotientKernel Γ f (x, y) * φ y ∂quotientMeasure Γ μ
        ∂quotientMeasure Γ μ := by
  set ν := quotientMeasure Γ μ with hν
  set Ψ := ContinuousMap.toLp 2 ν ℂ ψ
  set Φ := ContinuousMap.toLp 2 ν ℂ φ
  have hΨ : Ψ =ᵐ[ν] ψ := ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ) ψ
  have hΦ : Φ =ᵐ[ν] φ := ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ) φ
  have hcoef : ∀ g, ⟪Ψ, rightRegularRep Γ μ g Φ⟫_ℂ = ∫ x, conj (ψ x) * φ (rightMul Γ g x) ∂ν := by
    intro g
    rw [L2.inner_def]
    have h2 : (fun x => Φ (rightMul Γ g x)) =ᵐ[ν] fun x => φ (rightMul Γ g x) :=
      (measurePreserving_rightMul μ g).quasiMeasurePreserving.ae_eq_comp hΦ
    refine integral_congr_ae ?_
    filter_upwards [hΨ, coeFn_rightRegularRep Γ μ g Φ, h2] with x h1 h3 h4
    rw [h1, h3, h4, RCLike.inner_apply']
  have hF : Integrable (uncurry fun g x => f g * (conj (ψ x) * φ (rightMul Γ g x))) (μ.prod ν) := by
    have hc : Continuous (uncurry fun g x => f g * (conj (ψ x) * φ (rightMul Γ g x))) := by
      refine (f.continuous.comp continuous_fst).mul
        ((Complex.continuous_conj.comp (ψ.continuous.comp continuous_snd)).mul
          (φ.continuous.comp ?_))
      exact (continuous_rightMul_prod Γ).comp (continuous_snd.prodMk continuous_fst)
    refine hc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (f.hasCompactSupport.prod isCompact_univ) fun p hp => ?_
    have : p.1 ∉ tsupport f := fun h => hp ⟨h, mem_univ _⟩
    simp [uncurry, image_eq_zero_of_notMem_tsupport this]
  rw [UnitaryRep.inner_integrated]
  calc ∫ g, (UnitaryRep.ccToL1 μ f) g * ⟪Ψ, rightRegularRep Γ μ g Φ⟫_ℂ ∂μ
      = ∫ g, f g * ∫ x, conj (ψ x) * φ (rightMul Γ g x) ∂ν ∂μ :=
        integral_congr_ae ((coeFn_compactSupportToL1 μ f).mono fun g hg => by simp only [hg, hcoef g])
    _ = ∫ g, ∫ x, f g * (conj (ψ x) * φ (rightMul Γ g x)) ∂ν ∂μ := by
        simp_rw [← integral_const_mul]
    _ = ∫ x, ∫ g, f g * (conj (ψ x) * φ (rightMul Γ g x)) ∂μ ∂ν := integral_integral_swap hF
    _ = ∫ x, conj (ψ x) * ∫ g, f g * φ (rightMul Γ g x) ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [← integral_const_mul]
        congr 1
        ext g
        ring
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [integral_mul_rightMul_eq Γ μ f φ x]

omit [μ.IsMulRightInvariant] in

theorem inner_kernelOperator_toLp (f : CompactlySupportedContinuousMap G ℂ)
    (φ ψ : C(RightCosetSpace Γ, ℂ)) :
    ⟪ContinuousMap.toLp 2 (quotientMeasure Γ μ) ℂ ψ,
      kernelOperator Γ μ f (ContinuousMap.toLp 2 (quotientMeasure Γ μ) ℂ φ)⟫_ℂ =
      ∫ x, conj (ψ x) * ∫ y, quotientKernel Γ f (x, y) * φ y ∂quotientMeasure Γ μ
        ∂quotientMeasure Γ μ := by
  set ν := quotientMeasure Γ μ with hν
  set Ψ := ContinuousMap.toLp 2 ν ℂ ψ
  set Φ := ContinuousMap.toLp 2 ν ℂ φ
  have hΨ : Ψ =ᵐ[ν] ψ := ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ) ψ
  have hΦ : Φ =ᵐ[ν] φ := ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ) φ
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hΨ, L2Kernel.kernelOp_toLp_apply_ae (memLp_quotientKernel Γ μ f) Φ] with x h1 h2
  rw [kernelOperator, h1, h2, RCLike.inner_apply']
  congr 1
  exact integral_congr_ae (hΦ.mono fun y hy => by dsimp only; rw [hy])

theorem integrated_rightRegularRep_eq_kernelOperator (f : CompactlySupportedContinuousMap G ℂ) :
    (rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f) = kernelOperator Γ μ f := by
  set ν := quotientMeasure Γ μ
  have hD : DenseRange (ContinuousMap.toLp 2 ν ℂ : C(RightCosetSpace Γ, ℂ) →L[ℂ] Lp ℂ 2 ν) :=
    ContinuousMap.toLp_denseRange ℂ ν ℂ ENNReal.ofNat_ne_top
  have h2 : ∀ φ : C(RightCosetSpace Γ, ℂ),
      (rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f) (ContinuousMap.toLp 2 ν ℂ φ) =
        kernelOperator Γ μ f (ContinuousMap.toLp 2 ν ℂ φ) := fun φ =>
    ext_inner_left ℂ fun w => hD.induction_on w
      (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const))
      fun ψ => by rw [inner_integrated_toLp, inner_kernelOperator_toLp]
  refine ContinuousLinearMap.ext fun v => ?_
  exact congrFun (hD.equalizer (ContinuousLinearMap.continuous _)
    (ContinuousLinearMap.continuous _) (funext h2)) v

theorem isHilbertSchmidt_integrated_rightRegularRep (f : CompactlySupportedContinuousMap G ℂ) :
    IsHilbertSchmidt ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)) := by
  rw [integrated_rightRegularRep_eq_kernelOperator]
  exact isHilbertSchmidt_kernelOperator Γ μ f

theorem isCompactOperator_integrated_rightRegularRep (f : CompactlySupportedContinuousMap G ℂ) :
    IsCompactOperator ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)) :=
  (isHilbertSchmidt_integrated_rightRegularRep Γ μ f).isCompactOperator

end Operator

end RightCosetSpace

end

end GroundTheory.Automorphic
