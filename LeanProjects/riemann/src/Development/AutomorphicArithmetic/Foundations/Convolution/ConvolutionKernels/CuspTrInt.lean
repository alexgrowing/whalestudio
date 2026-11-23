import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.HsOfKer
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TraceKer
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAdj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopPc
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KvCont
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TwAdj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.NormLeOfSq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QmapPres
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.cuspTrInt :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ) (f a g : CC K n) (M : L2 μ →L[ℂ] L2 μ),
      CuspDecay μ a → CuspDecay μ (ccStar g) → M ∘L Pc μ = Pc μ ∘L M → Rop μ f = Rop μ a ∘L M ∘L Rop μ g →
      Integrable (fun y : RightCosetSpace (Gam K n) =>
        ⟪Pc μ (kv μ a (Quotient.out y)), M (Pc μ (kv μ (ccStar g) (θ.e (Quotient.out y))))⟫_ℂ) (quotientMeasure (Gam K n) μ) ∧
      cuspTr μ θ f = ∫ y : RightCosetSpace (Gam K n),
        ⟪Pc μ (kv μ a (Quotient.out y)), M (Pc μ (kv μ (ccStar g) (θ.e (Quotient.out y))))⟫_ℂ ∂quotientMeasure (Gam K n) μ := by
  intro K _ _ n μ _ θ f a g M ha hg hM hf
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  haveI : SecondCountableTopology (RightCosetSpace (Gam K n)) :=
    (isOpenQuotientMap_mk (Gam K n)).isQuotientMap.secondCountableTopology (isOpenQuotientMap_mk (Gam K n)).isOpenMap
  haveI : MeasurableSpace.CountablyGenerated (RightCosetSpace (Gam K n)) := BorelSpace.countablyGenerated
  haveI : IsSeparable (quotientMeasure (Gam K n) μ) := isSeparable_of_sigmaFinite _
  haveI : SecondCountableTopology (Lp ℂ 2 (quotientMeasure (Gam K n) μ)) := Lp.SecondCountableTopology
  haveI : TopologicalSpace.SeparableSpace (Lp ℂ 2 (quotientMeasure (Gam K n) μ)) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  obtain ⟨h1, q1⟩ := qmapPres (Gam K n) μ θ.e θ.mem_gam θ.pres
  have hout : ∀ (b : CC K n) (x : G1 K n), kv μ b (Quotient.out (mk (Gam K n) x)) = kv μ b x := by
    intro b x
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (show mk (Gam K n) (Quotient.out (mk (Gam K n) x)) = mk (Gam K n) x from Quotient.out_eq _)
    rw [← hγ]
    exact (ropAe K n μ b).2 _ γ.2 x
  have hmem : ∀ b : CC K n, CuspDecay μ b →
      MemLp (fun y : RightCosetSpace (Gam K n) => Pc μ (kv μ b (Quotient.out y))) 2 (quotientMeasure (Gam K n) μ) := by
    intro b hb
    obtain ⟨C, -, hC⟩ := (kvBd K n μ b).2 hb 0
    have hc : Continuous fun y : RightCosetSpace (Gam K n) => Pc μ (kv μ b (Quotient.out y)) :=
      (isOpenQuotientMap_mk (Gam K n)).isQuotientMap.continuous_iff.2
        (((Pc μ).continuous.comp (kvCont K n μ b)).congr fun x => by simp only [Function.comp_apply, hout])
    exact MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun y => by simpa using hC _)
  have hsa : ∀ u w : L2 μ, ⟪Pc μ u, w⟫_ℂ = ⟪u, Pc μ w⟫_ℂ := fun u w => Submodule.inner_starProjection_left_eq_right _ _ _
  have hPP : ∀ u : L2 μ, Pc μ (Pc μ u) = Pc μ u := fun u =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)
  have hker : ∀ (b : CC K n) (φ : L2 μ), ((Rop μ b ∘L Pc μ) φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
      fun y => ⟪Pc μ (kv μ b (Quotient.out y)), φ⟫_ℂ := by
    intro b φ
    simp only [hsa]
    exact (ropAe K n μ b).1 (Pc μ φ)
  have m1 := hmem a ha
  have m2 : MemLp (fun y : RightCosetSpace (Gam K n) => Pc μ (kv μ (ccStar g) (θ.e (Quotient.out y)))) 2
      (quotientMeasure (Gam K n) μ) := by
    have := (hmem _ hg).comp_measurePreserving q1
    simpa only [Function.comp_def, hout] using this
  have hPadj : ContinuousLinearMap.adjoint (Pc μ) = Pc μ :=
    ((ContinuousLinearMap.eq_adjoint_iff _ _).2 hsa).symm
  have hB : ContinuousLinearMap.adjoint (Pc μ ∘L Rop μ g ∘L θ.U) =
      ContinuousLinearMap.adjoint θ.U ∘L (Rop μ (ccStar g) ∘L Pc μ) := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, ropAdj, hPadj]
    rfl
  have hBk : ∀ φ : L2 μ, (ContinuousLinearMap.adjoint (Pc μ ∘L Rop μ g ∘L θ.U) φ : RightCosetSpace (Gam K n) → ℂ)
      =ᵐ[quotientMeasure (Gam K n) μ] fun y => ⟪Pc μ (kv μ (ccStar g) (θ.e (Quotient.out y))), φ⟫_ℂ := by
    intro φ
    rw [hB]
    refine (twAdj K n μ θ _).trans ?_
    have := q1.quasiMeasurePreserving.ae_eq_comp (hker (ccStar g) φ)
    simp only [Function.comp_def, hout] at this
    exact this
  have sA := hsOfKer _ _ _ m1 (hker a)
  have sB : IsHilbertSchmidt (Pc μ ∘L Rop μ g ∘L θ.U) := by
    have := (hsOfKer _ _ _ m2 hBk).adjoint
    rwa [ContinuousLinearMap.adjoint_adjoint] at this
  refine ⟨?_, ?_⟩
  · have m3 := M.comp_memLp' m2
    refine (m1.norm.integrable_mul m3.norm).mono' (m1.1.inner m3.1) (Filter.Eventually.of_forall fun y => ?_)
    exact norm_inner_le_norm _ _
  · rw [← traceKer _ _ M _ _ _ m1 m2 sA sB (hker a) hBk, cuspTr]
    congr 1
    ext1 φ
    have c1 : ∀ b (u : L2 μ), Rop μ b (Pc μ u) = Pc μ (Rop μ b u) := fun b u => DFunLike.congr_fun (ropPc K n μ b) u
    have c2 : ∀ u : L2 μ, M (Pc μ u) = Pc μ (M u) := fun u => DFunLike.congr_fun hM u
    have c3 : ∀ u : L2 μ, θ.U (Pc μ u) = Pc μ (θ.U u) := fun u => DFunLike.congr_fun θ.U_comm u
    rw [hf]
    simp only [ContinuousLinearMap.comp_apply, c1, c2, c3, hPP]
