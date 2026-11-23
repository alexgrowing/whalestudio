import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommInt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AdjInt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Unimod
import GroundTheory.AutomorphicForms.CuspidalProjection.OrthogonalProjectionOntoCompSubtypeL
import GroundTheory.AutomorphicForms.CompactFormulaSums

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem ccToL1_smul {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (c : ℂ) (f : CompactlySupportedContinuousMap G ℂ) :
    UnitaryRep.ccToL1 μ (c • f) = c • UnitaryRep.ccToL1 μ f := by
  unfold UnitaryRep.ccToL1
  rw [← MemLp.toLp_const_smul]
  rfl

private theorem norm_int_le {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : CompactlySupportedContinuousMap G ℂ) :
    ‖π.integrated μ (UnitaryRep.ccToL1 μ f)‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  have hf1 : ((UnitaryRep.ccToL1 μ f : G →₁[μ] ℂ) : G → ℂ) =ᵐ[μ] f := by
    unfold UnitaryRep.ccToL1
    exact MemLp.coeFn_toLp _
  refine (π.norm_integrated_le μ _).trans (le_of_eq ?_)
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (hf1.mono fun x hx => by simp only [hx])

private theorem int_add {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f g : CompactlySupportedContinuousMap G ℂ) :
    π.integrated μ (UnitaryRep.ccToL1 μ (f + g)) =
      π.integrated μ (UnitaryRep.ccToL1 μ f) + π.integrated μ (UnitaryRep.ccToL1 μ g) := by
  rw [UnitaryRep.ccToL1_add, map_add]

private theorem int_smul {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (c : ℂ) (f : CompactlySupportedContinuousMap G ℂ) :
    π.integrated μ (UnitaryRep.ccToL1 μ (c • f)) = c • π.integrated μ (UnitaryRep.ccToL1 μ f) := by
  rw [ccToL1_smul, map_smul]

private theorem int_commute {G G₁ H : Type} [Group G] [TopologicalSpace G] [Group G₁] [TopologicalSpace G₁]
    [MeasurableSpace G₁] [OpensMeasurableSpace G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (p : G₁ →* G) (hp : Continuous p) (μ : Measure G₁) [IsFiniteMeasureOnCompacts μ]
    (f : G₁ →₁[μ] ℂ) (x : G) (hx : ∀ a, x * p a = p a * x) :
    Commute ((π.compHom p hp).integrated μ f) (π x) := by
  have hT : π x ∈ (π.compHom p hp).intertwiners (π.compHom p hp) := by
    intro a v
    show π x (π (p a) v) = π (p a) (π x v)
    rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, hx]
  exact (UnitaryRep.comp_integrated_of_mem_intertwiners _ μ hT f).symm

theorem UpperTheory.ConvolutionTheory.Tf.opAlg :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure],
      (∀ β β' : TI K n, Oinf μ ν (conv ν β β') = Oinf μ ν β ∘L Oinf μ ν β' ∧ Oinf μ ν (β + β') = Oinf μ ν β + Oinf μ ν β') ∧
      (∀ e e' : TF K n, Ofin μ m (conv m e e') = Ofin μ m e ∘L Ofin μ m e' ∧ Ofin μ m (e + e') = Ofin μ m e + Ofin μ m e') ∧
      (∀ (c : ℂ) (β : TI K n) (e : TF K n), Oinf μ ν (c • β) = c • Oinf μ ν β ∧ Ofin μ m (c • e) = c • Ofin μ m e) ∧
      (∀ β β' : TI K n, (∀ x, β' x = conj (β x⁻¹)) → ContinuousLinearMap.adjoint (Oinf μ ν β) = Oinf μ ν β') ∧
      (∀ e e' : TF K n, (∀ x, e' x = conj (e x⁻¹)) → ContinuousLinearMap.adjoint (Ofin μ m e) = Ofin μ m e') ∧
      (∀ β : TI K n, ‖Oinf μ ν β‖ ≤ ∫ x, ‖β x‖ ∂ν) ∧ (∀ e : TF K n, ‖Ofin μ m e‖ ≤ ∫ x, ‖e x‖ ∂m) ∧
      (∀ (β : TI K n) (e : TF K n), Commute (Oinf μ ν β) (Ofin μ m e)) ∧
      ∀ (β : TI K n) (h : AdelicGLn.FiniteAdelicGL K n), Commute (Oinf μ ν β) (rhoF μ h) := by
  intro K _ _ n μ _ ν _ m _
  obtain ⟨hν₁, hν₂⟩ := (Tf.unimod K n).1 ν
  obtain ⟨hm₁, hm₂⟩ := (Tf.unimod K n).2 m
  have hpq : ∀ (a : archGroup K n) (b : AdelicGLn.FiniteAdelicGL K n),
      archP K n a * MultiplicityOne.finProj K n b = MultiplicityOne.finProj K n b * archP K n a :=
    fun a b => (MultiplicityOne.finProj_mul_archProj_comm b (a : ArchUnits K n)).symm
  refine ⟨fun β β' => ⟨?_, ?_⟩, fun e e' => ⟨?_, ?_⟩, fun c β e => ⟨?_, ?_⟩, fun β β' h => ?_, fun e e' h => ?_,
    fun β => ?_, fun e => ?_, fun β e => ?_, fun β h => ?_⟩
  · exact CuspidalProjection.integrated_conv ν _ β β'
  · exact int_add _ ν β β'
  · exact CuspidalProjection.integrated_conv m _ e e'
  · exact int_add _ m e e'
  · exact int_smul _ ν c β
  · exact int_smul _ m c e
  · exact (Tf.adjInt _ _ _ ν β β' h).1
  · exact (Tf.adjInt _ _ _ m e e' h).1
  · exact norm_int_le _ ν β
  · exact norm_int_le _ m e
  · exact (Tf.commInt _ _ _ _ (rightRegularRep (rationalGLOne K n) μ) (archP K n) continuous_archP
      (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj ν m β e).2 hpq
  · exact int_commute _ (archP K n) continuous_archP ν _ (MultiplicityOne.finProj K n h) fun a => (hpq a h).symm
