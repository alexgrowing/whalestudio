import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.AdelicGluing.OfinDoubleCosetIndicatorEqHop
import Development.AutomorphicArithmetic.AdelicGluing.HeckeOperatorAdjointInvEqHeckeOperator
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem ind_sum {G : Type*} [Group G] (J : Subgroup G) (x : G) (t : Finset (G ⧸ J))
    (ht : ∀ c, c ∈ t ↔ ∃ k ∈ J, c = QuotientGroup.mk (k * x)) (g : G) :
    ∑ c ∈ t, (J : Set G).indicator (1 : G → ℂ) (c.out⁻¹ * g) = {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b}.indicator 1 g := by
  classical
  have h1 : ∀ c : G ⧸ J, (J : Set G).indicator (1 : G → ℂ) (c.out⁻¹ * g) = if (QuotientGroup.mk g : G ⧸ J) = c then 1 else 0 := fun c => by
    have : c.out⁻¹ * g ∈ (J : Set G) ↔ (QuotientGroup.mk g : G ⧸ J) = c := by
      rw [SetLike.mem_coe, ← QuotientGroup.eq, QuotientGroup.out_eq']
      exact eq_comm
    simp only [Set.indicator_apply, this, Pi.one_apply]
  have h2 : (QuotientGroup.mk g : G ⧸ J) ∈ t ↔ ∃ a ∈ J, ∃ b ∈ J, g = a * x * b := by
    rw [ht]
    refine exists_congr fun a => and_congr_right fun _ => ⟨fun e => ⟨(a * x)⁻¹ * g, QuotientGroup.eq.1 e.symm, by group⟩, ?_⟩
    rintro ⟨b, hb, rfl⟩
    exact QuotientGroup.mk_mul_of_mem _ hb
  simp only [h1, Finset.sum_ite_eq, h2, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]

private theorem conj_ind {G : Type*} (A B : Set G) (g g' : G) (h : g ∈ A ↔ g' ∈ B) :
    conj (A.indicator (1 : G → ℂ) g) = B.indicator 1 g' := by
  classical
  simp only [Set.indicator_apply, h, Pi.one_apply]
  split_ifs <;> simp

private theorem commute_of_adjoint_factorisations {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A A' E₀ E₁ F₀ F₁ : H →L[ℂ] H)
    (s1 : E₁ = A ∘L E₀) (s2 : F₁ = A' ∘L F₀) (a0 : ContinuousLinearMap.adjoint E₀ = F₀) (a1 : ContinuousLinearMap.adjoint E₁ = F₁)
    (a : ContinuousLinearMap.adjoint A' = A) : Commute A E₀ := by
  rw [← a0, ← a1] at s2
  have s3 := congrArg ContinuousLinearMap.adjoint s2
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_adjoint, a] at s3
  exact s1.symm.trans s3

set_option maxHeartbeats 1000000 in
theorem UpperTheory.commute_heckeOperator_finiteConvolution_of_free_indicator :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
          (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) →
          ∀ (x : GL (Fin n) (w.adicCompletion K)) (r : AdelicGLn.FiniteAdelicGL K n → ℂ), Free w r → ∀ e₀ : TF K n,
            (∀ y, e₀ y = r y * (J : Set (GL (Fin n) (w.adicCompletion K))).indicator 1 (cf w y)) → Commute (Hop μ w J x) (Ofin μ m e₀) := by
  intro K _ _ n hn μ _ m _ w J hJ hc x r hr e₀ h0
  obtain ⟨-, l1, -, -, l2⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
  have cm : ∀ a b : AdelicGLn.FiniteAdelicGL K n, cf w (a * b) = cf w a * cf w b := fun a b => by
    unfold cf
    rw [map_mul, finAt_mul]
  have cl : ∀ a, cf w (AdelicGLn.localEmbedding w a) = a := l1
  have c1 : cf w (1 : AdelicGLn.FiniteAdelicGL K n) = 1 := by simpa using cl 1
  have ci : ∀ a : AdelicGLn.FiniteAdelicGL K n, cf w a⁻¹ = (cf w a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_left (by rw [← cm, inv_mul_cancel, c1])
  have hr' : ∀ y a, r (y * AdelicGLn.localEmbedding w a) = r y := fun y a => by
    have h1 : cf w (AdelicGLn.localEmbedding w (cf w y)⁻¹ * y) = 1 := by rw [cm, cl, inv_mul_cancel]
    rw [← hr (cf w y)⁻¹, ← mul_assoc, ← l2 _ h1 a, hr, hr]
  have hfin := (UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x hJ hc).1
  let tr : AdelicGLn.FiniteAdelicGL K n → TF K n := fun a =>
    ⟨⟨fun y => e₀ (a * y), e₀.continuous.comp (continuous_const_mul a)⟩, e₀.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft a)⟩
  let e₁ : TF K n := ∑ c ∈ hfin.toFinset, tr (AdelicGLn.localEmbedding w c.out⁻¹)
  have h1 : ∀ y, e₁ y = r y * {g : GL (Fin n) (w.adicCompletion K) | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b}.indicator 1 (cf w y) := fun y => by
    rw [← ind_sum J x hfin.toFinset (fun c => hfin.mem_toFinset), Finset.mul_sum, CompactlySupportedContinuousMap.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    show e₀ (_ * y) = _
    rw [h0, hr, cm, cl]
  let st : TF K n → TF K n := fun e => ⟨⟨fun y => conj (e y⁻¹), Complex.continuous_conj.comp (e.continuous.comp continuous_inv)⟩,
    (e.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z : ℂ => conj z) (map_zero _)⟩
  have hst : ∀ e y, st e y = conj (e y⁻¹) := fun _ _ => rfl
  have s1 := UpperTheory.Ofin_doubleCoset_indicator_eq_Hop K n hn μ m w J x hJ hc r hr e₀ e₁ h0 h1
  have s2 := UpperTheory.Ofin_doubleCoset_indicator_eq_Hop K n hn μ m w J x⁻¹ hJ hc (fun y => conj (r y⁻¹)) (fun a y => by
      show conj (r _) = conj (r _)
      rw [mul_inv_rev, ← map_inv, hr']) (st e₀) (st e₁)
    (fun y => by
      rw [hst, h0, map_mul, ci]
      exact congrArg _ (conj_ind _ _ _ _ J.inv_mem_iff))
    (fun y => by
      rw [hst, h1, map_mul, ci]
      refine congrArg _ (conj_ind _ _ _ _ ⟨?_, ?_⟩)
      · rintro ⟨a, ha, b, hb, e⟩
        exact ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, by rw [← inv_inv (cf w y), e]; group⟩
      · rintro ⟨a, ha, b, hb, e⟩
        exact ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, by rw [e]; group⟩)
  have ad := (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ Measure.haar m).2.2.2.2.1
  exact commute_of_adjoint_factorisations _ _ _ _ _ _ s1 s2 (ad e₀ _ (hst e₀)) (ad e₁ _ (hst e₁)) (UpperTheory.heckeOperator_adjoint_inv_eq_heckeOperator K n μ w J hJ hc x)
