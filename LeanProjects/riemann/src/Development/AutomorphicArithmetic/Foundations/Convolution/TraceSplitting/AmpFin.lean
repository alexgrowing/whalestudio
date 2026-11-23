import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OpBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigSummands
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandsSpan
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvExSub
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import GroundTheory.AutomorphicForms.CompactSelfAdjoint

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

private theorem exists_pos_eig {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (hVW : V ≤ W) (A : H →L[ℂ] H) (hA : 0 ≤ A)
    (hAV : ∀ v ∈ V, A v ∈ V) (hc : IsCompactOperator (A ∘L prj W)) (h : ∃ v ∈ V, A v ≠ 0) :
    ∃ x : ℝ, 0 < x ∧ eigIn V A x ≠ ⊥ := by
  have hs : IsSelfAdjoint A := GroundTheory.Automorphic.isSelfAdjoint_of_nonneg hA
  have hcl : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hPV : ∀ v, prj V v ∈ V := fun v => by
    have h1 : prj V v ∈ V.topologicalClosure := V.topologicalClosure.starProjection_apply_mem v
    rwa [hcl] at h1
  have hPfix : ∀ v ∈ V, prj V v = v := fun v hv =>
    Submodule.starProjection_eq_self_iff.2 (by rw [hcl]; exact hv)
  have hWfix : ∀ v, prj W (prj V v) = prj V v := fun v =>
    Submodule.starProjection_eq_self_iff.2 (W.le_topologicalClosure (hVW (hPV v)))
  have hPs : ContinuousLinearMap.adjoint (prj V) = prj V :=
    (ContinuousLinearMap.isSelfAdjoint_iff'.1 (isSelfAdjoint_starProjection _))
  set B : H →L[ℂ] H := prj V ∘L A ∘L prj V with hB
  have hBc : IsCompactOperator B := by
    have e : B = prj V ∘L ((A ∘L prj W) ∘L prj V) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [hB, ContinuousLinearMap.comp_apply, hWfix]
    rw [e]
    exact (hc.comp_clm (prj V)).clm_comp (prj V)
  have hBs : IsSelfAdjoint B := by
    have h1 := hs.conj_adjoint (prj V)
    rwa [hPs] at h1
  have hBv : ∀ v ∈ V, B v = A v := fun v hv => by
    simp only [hB, ContinuousLinearMap.comp_apply, hPfix v hv, hPfix _ (hAV v hv)]
  obtain ⟨s, b, l, -, hTb₀, hsum, -⟩ := GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum hBc hBs
  have hTb : ∀ i, B (b i) = ((l i : ℝ) : ℂ) • b i := fun i => by
    rw [hTb₀ i]
    rfl
  obtain ⟨v, hv, hv0⟩ := h
  obtain ⟨i, hi⟩ : ∃ i, l i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : HasSum (fun i => (((l i : ℝ) : ℂ) * ⟪b i, v⟫_ℂ) • b i) (0 : H) := by
      simp only [hcon, Complex.ofReal_zero, zero_mul, zero_smul]
      exact hasSum_zero
    exact hv0 (by rw [← hBv v hv]; exact (hsum v).unique h0)
  have hw0 : b i ≠ 0 := b.orthonormal.ne_zero i
  have hli : ((l i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hi
  have hwV : b i ∈ V := by
    have h1 : b i = ((l i : ℝ) : ℂ)⁻¹ • B (b i) := by
      rw [hTb i, smul_smul, inv_mul_cancel₀ hli, one_smul]
    rw [h1]
    exact V.smul_mem _ (hPV _)
  have hAw : A (b i) = ((l i : ℝ) : ℂ) • b i := by rw [← hBv _ hwV, hTb i]
  have hpos : 0 < l i := by
    have h1 := ((ContinuousLinearMap.nonneg_iff_isPositive A).1 hA).re_inner_nonneg_right (b i)
    have hn : ⟪b i, b i⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
      simp
    rw [hAw, inner_smul_right, hn] at h1
    simp only [mul_one, RCLike.re_to_complex, Complex.ofReal_re] at h1
    exact lt_of_le_of_ne h1 hi.symm
  refine ⟨l i, hpos, (Submodule.ne_bot_iff _).2 ⟨b i, Submodule.mem_inf.2 ⟨hwV, ?_⟩, hw0⟩⟩
  exact Module.End.mem_eigenspace_iff.2 hAw

theorem UpperTheory.ConvolutionTheory.T.ampFin :
    UpperTheory.ConvolutionTheory.T.AmpFin := by
  intro K _ _ _ n hn μ _ 𝔞
  obtain ⟨hA0, -, -, -⟩ := UpperTheory.ConvolutionTheory.evEx K n hn μ 𝔞
  have hUc : IsCompact (𝔞.U : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (𝔞.U.isClosed_of_isOpen 𝔞.isOpen)
      fun _ h => 𝔞.le h
  obtain ⟨m, hm, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ 𝔞.ν
  haveI := hm
  obtain ⟨e, -, he⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m 𝔞.U 𝔞.isOpen hUc
  have hAR : RR μ (tens 𝔞.a₀ e) = 𝔞.A := by
    rw [UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ 𝔞.ν m hC, he]
    rfl
  obtain ⟨hsum, hcusp, hcpt⟩ := opBasics K n μ (tens 𝔞.a₀ e)
  rw [hAR] at hsum hcusp hcpt
  have hs : IsSelfAdjoint 𝔞.A := GroundTheory.Automorphic.isSelfAdjoint_of_nonneg hA0
  refine ⟨fun x hx => ?_, fun V hV hv =>
    exists_pos_eig (cuspidalL2 μ) V hV.closed hV.le 𝔞.A hA0 (hsum V hV) hcpt hv⟩
  have hfd : FiniteDimensional ℂ (eigIn (cuspidalL2 μ) 𝔞.A x) := by
    obtain ⟨S, hS, hf, -⟩ := eigSplit (LL μ) (cuspidalL2 μ) 𝔞.A (isClosed_cuspidalL2 μ) hA0 hcusp hcpt (x / 2) (by linarith)
    by_cases h : eigIn (cuspidalL2 μ) 𝔞.A x = ⊥
    · rw [h]
      infer_instance
    · exact hf x ((hS x).2 ⟨by linarith, h⟩)
  obtain ⟨s, hs', -⟩ := eigSummands (LL μ) {V : Submodule ℂ (LL μ) // IsSummand μ V} (fun i => i.1) (cuspidalL2 μ) 𝔞.A x
    (fun i => i.2.closed) (fun i j hij => Dp.multiplicity_one_cuspidal_spectrum_normOneGL K n μ i.1 j.1 i.2 j.2 fun h => hij (Subtype.ext h))
    (summandsSpan K n μ) hs (fun i => hsum i.1 i.2) hfd
  classical
  refine (s.image Subtype.val).finite_toSet.subset ?_
  rintro V ⟨hV, hne⟩
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨V, hV⟩, (hs' _).2 hne, rfl⟩)
