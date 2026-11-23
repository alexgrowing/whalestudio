import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.TwistedTraces.LeClosureSpanAllOfCommutingUnitaryReps
import Development.AutomorphicArithmetic.TwistedTraces.IntegralOperatorFixedInvariantOfLeftInvariantKer
import Development.AutomorphicArithmetic.TwistedTraces.SummandLeClosureSpanLocalTypeImages

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem trace_sub {E : Type} [AddCommGroup E] [Module ℂ E] (W W' : Submodule ℂ E) (hle : W ≤ W')
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ W'] (a : E →ₗ[ℂ] E) (h : ∀ x ∈ W', a x ∈ W)
    (b : Module.End ℂ W) (b' : Module.End ℂ W') (hb : ∀ x : W, (b x : E) = a x) (hb' : ∀ x : W', (b' x : E) = a x) :
    LinearMap.trace ℂ W' b' = LinearMap.trace ℂ W b := by
  let p : W' →ₗ[ℂ] W := (a ∘ₗ W'.subtype).codRestrict W fun x => h x x.2
  let q : W →ₗ[ℂ] W' := Submodule.inclusion hle
  have e1 : b' = q ∘ₗ p := by
    ext x
    rw [hb']
    rfl
  have e2 : b = p ∘ₗ q := by
    ext x
    rw [hb]
    rfl
  rw [e1, e2, LinearMap.trace_comp_comm']

theorem UpperTheory.ConvolutionTheory.C.summandFactor :
    UpperTheory.ConvolutionTheory.C.SummandFactor := by
  intro K _ _ n μ _ V Z r w _ _ σ hV hw hσ hZV hZ0 hZc hZi hadm
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
  obtain ⟨hfd, N, hN, key⟩ := UpperTheory.le_closure_spanAll_of_commuting_unitaryReps r (fun i => Gw n (w i)) (LL μ) (fun i => (σ i).V)
    (fun i => locU μ (w i)) (fun i => (σ i).ρ) V Z (fun i => (σ i).smooth) (fun i => (σ i).irred) hcomm hZc hZV hinv
    (fun i => UpperTheory.summand_le_closure_span_local_type_images K n μ V (w i) (σ i) hV (hσ i)) (fun U hU => by rw [hfix]; exact hadm U hU) hZ0
  refine ⟨N, hN, ?_⟩
  intro U m φ T s hU hm _ hφ hT hs
  choose A hA hAs using hs
  have hf := fun i => by
    haveI := hm i
    exact UpperTheory.integralOperator_fixed_invariant_of_left_invariant_kernel (Gw n (w i)) (LL μ) (σ i).V (locU μ (w i)) (σ i).ρ (m i) (φ i) (T i) (A i) (U i)
      (fun u v => hT i u v) (hA i) (hφ i)
  haveI := fun i => hfd U hU i
  let B : ∀ i, Module.End ℂ (fixedVectors (σ i).ρ (U i)) := fun i =>
    (A i).restrict fun x _ => (hf i).2.1 x
  have hB : ∀ i, LinearMap.trace ℂ (fixedVectors (σ i).ρ (U i)) (B i) = s i := by
    intro i
    obtain ⟨h1, h2⟩ := hAs i
    rw [← h2]
    exact trace_sub (LinearMap.range (A i)) (fixedVectors (σ i).ρ (U i))
      (by rintro _ ⟨x, rfl⟩; exact (hf i).2.1 x) (A i) (fun x _ => LinearMap.mem_range_self _ x) _ _
      (fun x => rfl) (fun x => rfl)
  have hfin := key U hU T A B (fun i v => (hf i).1 v) (fun i v hv => (hf i).2.2.1 Z hZc (hinv i) v hv)
    (fun i j hij h v => (hf i).2.2.2.1 (locU μ (w j) h)
      (fun g v => hcomm i j hij g h v)
      (fun g v => by rw [UnitaryRep.adjoint_map]; exact hcomm i j hij g h⁻¹ v) v)
    (fun i f hf' x => (hf i).2.2.2.2 f hf' x) (fun i x => (hf i).2.1 x) (fun i x => rfl)
  rw [hfix] at hfin
  rw [hfin]
  simp only [hB]
