import Mathlib
import GroundTheory.AutomorphicForms.CuspidalProjection.Global
import GroundTheory.AutomorphicForms.TraceClass
import GroundTheory.AutomorphicForms.TraceFormulaConvolution

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise InnerProductSpace ComplexConjugate NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalProjection

section Conv

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)

theorem inner_integrated_ccToL1 (f : CompactlySupportedContinuousMap G ℂ) (w u : H) :
    ⟪w, π.integrated μ (UnitaryRep.ccToL1 μ f) u⟫_ℂ = ∫ g, f g * ⟪w, π g u⟫_ℂ ∂μ := by
  rw [UnitaryRep.inner_integrated]
  refine integral_congr_ae ((MemLp.coeFn_toLp (μ := μ)
    (f.continuous.memLp_of_hasCompactSupport (p := 1) f.hasCompactSupport)).mono fun g hg => ?_)
  dsimp only
  exact congrArg (· * ⟪w, π g u⟫_ℂ) hg

theorem integrated_conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    π.integrated μ (UnitaryRep.ccToL1 μ (conv μ f₁ f₂)) =
      π.integrated μ (UnitaryRep.ccToL1 μ f₁) ∘L π.integrated μ (UnitaryRep.ccToL1 μ f₂) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  set Φ : G → G → ℂ := fun x g => f₁ g * f₂ (g⁻¹ * x) * ⟪w, π x v⟫_ℂ with hΦ
  have hcont : Continuous (uncurry Φ) :=
    ((f₁.continuous.comp continuous_snd).mul
      (f₂.continuous.comp (continuous_snd.inv.mul continuous_fst))).mul
      (continuous_const.inner ((π.continuous_orbit v).comp continuous_fst))
  have hsupp : HasCompactSupport (uncurry Φ) := by
    refine HasCompactSupport.intro
      ((f₁.hasCompactSupport.isCompact.mul f₂.hasCompactSupport.isCompact).prod
        f₁.hasCompactSupport.isCompact) fun p hp => ?_
    obtain ⟨x, g⟩ := p
    show f₁ g * f₂ (g⁻¹ * x) * ⟪w, π x v⟫_ℂ = 0
    by_cases h1 : g ∈ tsupport f₁
    · by_cases h2 : g⁻¹ * x ∈ tsupport f₂
      · exact absurd ⟨⟨g, h1, g⁻¹ * x, h2, by simp⟩, h1⟩ hp
      · rw [image_eq_zero_of_notMem_tsupport h2, mul_zero, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul, zero_mul]
  have hint : Integrable (uncurry Φ) (μ.prod μ) := hcont.integrable_of_hasCompactSupport hsupp
  calc ⟪w, π.integrated μ (UnitaryRep.ccToL1 μ (conv μ f₁ f₂)) v⟫_ℂ
      = ∫ x, (∫ g, f₁ g * f₂ (g⁻¹ * x) ∂μ) * ⟪w, π x v⟫_ℂ ∂μ := by
        rw [inner_integrated_ccToL1]
        rfl
    _ = ∫ x, ∫ g, Φ x g ∂μ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ g, ∫ x, Φ x g ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ g, f₁ g * ∫ x, f₂ x * ⟪w, π (g * x) v⟫_ℂ ∂μ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        dsimp only
        rw [← integral_mul_left_eq_self (fun x => Φ x g) g, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hΦ, inv_mul_cancel_left, mul_assoc]
    _ = ∫ g, f₁ g * ⟪w, π g (π.integrated μ (UnitaryRep.ccToL1 μ f₂) v)⟫_ℂ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        dsimp only
        rw [UnitaryRep.inner_map_right, inner_integrated_ccToL1]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [UnitaryRep.inner_map_left, inv_inv, ← UnitaryRep.map_mul_apply]
    _ = ⟪w, (π.integrated μ (UnitaryRep.ccToL1 μ f₁) ∘L
          π.integrated μ (UnitaryRep.ccToL1 μ f₂)) v⟫_ℂ := by
        rw [ContinuousLinearMap.comp_apply, inner_integrated_ccToL1]

end Conv

section Subspace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (V : Submodule ℂ H) [CompleteSpace V]

theorem orthogonalProjectionOnto_comp_subtypeL :
    V.orthogonalProjectionOnto ∘L V.subtypeL = ContinuousLinearMap.id ℂ V :=
  ContinuousLinearMap.ext fun w => V.orthogonalProjectionOnto_mem_subspace_eq_self w

theorem eq_orthogonalProjectionOnto_comp (T : V →L[ℂ] V) :
    T = V.orthogonalProjectionOnto ∘L (V.subtypeL ∘L T) := by
  rw [← ContinuousLinearMap.comp_assoc, orthogonalProjectionOnto_comp_subtypeL,
    ContinuousLinearMap.id_comp]

theorem isTraceClass_subtypeL_comp_comp {A B : V →L[ℂ] V} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) :
    IsTraceClass (V.subtypeL ∘L (A ∘L B) ∘L V.orthogonalProjectionOnto) := by
  have heq : V.subtypeL ∘L (A ∘L B) ∘L V.orthogonalProjectionOnto =
      (V.subtypeL ∘L A ∘L V.orthogonalProjectionOnto) ∘L
        (V.subtypeL ∘L B ∘L V.orthogonalProjectionOnto) := by
    conv_lhs => rw [show A ∘L B = A ∘L (V.orthogonalProjectionOnto ∘L V.subtypeL) ∘L B by
      rw [orthogonalProjectionOnto_comp_subtypeL, ContinuousLinearMap.id_comp]]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [heq]
  exact isTraceClass_comp ((hA.comp_right V.orthogonalProjectionOnto).comp_left V.subtypeL)
    ((hB.comp_right V.orthogonalProjectionOnto).comp_left V.subtypeL)

end Subspace

open Reduction AutomorphicForm CuspidalSpectrum RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem isHilbertSchmidt_cuspRep_of_bound (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (B : ℝ) (hB : ∀ φ ∈ cuspidalL2 μ, ∀ x, ‖rconv Γ₁ μ f φ x‖ ≤ B * ‖φ‖) :
    IsHilbertSchmidt ((cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ f)) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  let T := (cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ f)
  let T' : cuspidalL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ) := (cuspidalL2 μ).subtypeL ∘L T
  have hT' : T' = (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L
      (cuspidalL2 μ).subtypeL := subtypeL_comp_integrated μ _
  let e : RightCosetSpace Γ₁ → StrongDual ℂ (cuspidalL2 μ) := fun q =>
    (rconvCLM Γ₁ μ f (Quotient.out q)).comp (cuspidalL2 μ).subtypeL
  have he : ∀ q, ‖e q‖ ≤ max B 0 := by
    intro q
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun w => ?_
    change ‖rconv Γ₁ μ f (w : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (Quotient.out q)‖ ≤ _
    refine (hB w w.2 _).trans ?_
    rw [Submodule.coe_norm]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hout : ∀ (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (q : RightCosetSpace Γ₁),
      rconvQ Γ₁ μ f φ q = rconv Γ₁ μ f φ (Quotient.out q) := by
    intro φ q
    obtain ⟨a, rfl⟩ := mk_surjective Γ₁ q
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Γ₁)).1 (Quotient.out_eq (mk Γ₁ a))
    rw [rconvQ_mk, ← hγ]
    exact (rconv_mul_left Γ₁ μ f φ γ.2 a).symm
  have hae : ∀ w, T' w =ᵐ[quotientMeasure Γ₁ μ] fun q => e q w := by
    intro w
    have h1 : T' w = (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f)
        (w : Lp ℂ 2 (quotientMeasure Γ₁ μ)) := by
      rw [hT']
      rfl
    rw [h1]
    filter_upwards [integrated_ae_eq_rconvQ Γ₁ μ f (w : Lp ℂ 2 (quotientMeasure Γ₁ μ))] with q hq
    exact hq.trans (hout _ q)
  have hHS : IsHilbertSchmidt T' := isHilbertSchmidt_of_ae_eq_dual T' e (max B 0) he hae
  have hTT : T = (cuspidalL2 μ).orthogonalProjectionOnto ∘L T' :=
    eq_orthogonalProjectionOnto_comp (cuspidalL2 μ) T
  show IsHilbertSchmidt T
  rw [hTT]
  exact hHS.comp_left _

theorem isHilbertSchmidt_cuspRep (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure]
    {β : ArchMatrix K n → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    IsHilbertSchmidt ((cuspRep μ).integrated μ
      (UnitaryRep.ccToL1 μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)))) :=
  Exists.elim (exists_norm_rconv_le_uniform μ ν hβ hβc hβu U hU g) fun B hB =>
    isHilbertSchmidt_cuspRep_of_bound μ _ B hB

theorem isTraceClass_cuspRep_conv (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure]
    {β₁ β₂ : ArchMatrix K n → ℝ} (hβ₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β₁)
    (hβ₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β₂) (hβc₁ : HasCompactSupport β₁)
    (hβc₂ : HasCompactSupport β₂)
    (hβu₁ : tsupport β₁ ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (hβu₂ : tsupport β₂ ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (U₁ U₂ : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU₁ : IsOpen (U₁ : Set (AdelicGLn.integralFiniteGL K n)))
    (hU₂ : IsOpen (U₂ : Set (AdelicGLn.integralFiniteGL K n)))
    (g₁ g₂ : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    IsTraceClass ((cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ
      (conv μ (archConv ν hβ₁.continuous hβc₁ hβu₁ (finAvg U₁ hU₁ g₁))
        (archConv ν hβ₂.continuous hβc₂ hβu₂ (finAvg U₂ hU₂ g₂))))) := by
  rw [integrated_conv]
  exact isTraceClass_comp (isHilbertSchmidt_cuspRep μ ν hβ₁ hβc₁ hβu₁ U₁ hU₁ g₁)
    (isHilbertSchmidt_cuspRep μ ν hβ₂ hβc₂ hβu₂ U₂ hU₂ g₂)

end CuspidalProjection

end

end GroundTheory.Automorphic
