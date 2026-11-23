import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.TwistedTraces.IsotypicMultiplicityTensorProduct
import Development.AutomorphicArithmetic.TwistedTraces.IntegralOperatorFixedInvariantOfLeftInvariantKer
import Development.AutomorphicArithmetic.TwistedTraces.SummandLeClosureSpanLocalTypeImages

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.ConvolutionTheory.C.twistFactor :
    UpperTheory.ConvolutionTheory.C.TwistFactor := by
  intro K _ _ n μ _ V Z r w _ _ τ s I R hV hw hτ hZV hZ0 hZi hadm hRZ hRs hI
  classical
  have hfix : ∀ U : ∀ i, Subgroup (Gw n (w i)),
      (Z ⊓ ⨅ i, fixU (locU μ (w i)) (U i)) = Z ⊓ ⨅ i, fixL μ (w i) (U i) := fun U => by
    simp only [fixU_locU]
  have hinv : ∀ i, (locU μ (w i)).IsInvariant Z := fun i g v hv => hZi i g v hv
  have hcomm : ∀ i j, i ≠ j → ∀ (g : Gw n (w i)) (h : Gw n (w j)) v,
      locU μ (w i) g (locU μ (w j) h v) = locU μ (w j) h (locU μ (w i) g v) := by
    intro i j hij g h v
    have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)).2.2.2.1 (w j) (fun e => hij (hw e.symm)) g h
    have e : ∀ (a : Gw n (w i)) (b : Gw n (w j)), (locU μ (w i) a) ((locU μ (w j) b) v) =
        rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding (w i) a *
          AdelicGLn.localEmbedding (w j) b)) v := by
      intro a b
      rw [map_mul, UnitaryRep.map_mul_apply]
      rfl
    have e' : (locU μ (w j) h) ((locU μ (w i) g) v) =
        rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding (w j) h *
          AdelicGLn.localEmbedding (w i) g)) v := by
      rw [map_mul, UnitaryRep.map_mul_apply]
      rfl
    exact (e g h).trans ((congrArg (fun u => rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n u) v) hc).trans e'.symm)
  obtain ⟨c, hc⟩ := UpperTheory.isotypic_multiplicity_tensor_product r (fun i => Gw n (w i)) (LL μ) (fun i => (τ i).V) (fun i => locU μ (w i))
    (fun i => (τ i).ρ) V Z (fun i => (τ i).smooth) (fun i => (τ i).irred) hcomm hZ0 hZV hinv
    (fun i => UpperTheory.summand_le_closure_span_local_type_images K n μ V (w i) (τ i) hV (hτ i)) (fun U hU => by rw [hfix]; exact hadm U hU)
    s I R hRZ (fun i g v hv => hRs i g v hv) hI
  refine ⟨c, ?_⟩
  intro U m φ T t hU hm _ hφ hT ht
  choose A hA hAt using ht
  have hf := fun i => by
    haveI := hm i
    exact UpperTheory.integralOperator_fixed_invariant_of_left_invariant_kernel (Gw n (w i)) (LL μ) (τ i).V (locU μ (w i)) (τ i).ρ (m i) (φ i) (T i) (A i) (U i)
      (fun u v => hT i u v) (hA i) (hφ i)
  have hfin := hc U T A t hU (fun i v => (hf i).1 v) (fun i v hv => (hf i).2.2.1 Z hZ0 (hinv i) v hv)
    (fun i j hij h v => (hf i).2.2.2.1 (locU μ (w j) h)
      (fun g v => hcomm i j hij g h v)
      (fun g v => by rw [UnitaryRep.adjoint_map]; exact hcomm i j hij g h⁻¹ v) v)
    (fun i f hf' x => (hf i).2.2.2.2 f hf' x) (fun i x => (hf i).2.1 x) hAt
  rw [hfix] at hfin
  exact hfin
