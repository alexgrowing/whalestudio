import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.finprod_local_eq_indicator_mul_prod :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K), Function.Injective w → ∀ (f : ∀ v : Pl K, Gw n v → ℂ),
          (∀ v, v ∉ Set.range w → f v = (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v)).indicator 1) → ∀ x : AdelicGLn.FiniteAdelicGL K n,
          ∏ᶠ v, f v (finAt v (finEmb K n x)) =
            ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator 1 x *
              ∏ i, f (w i) (finAt (w i) (finEmb K n x)) := by
  classical
  intro K _ _ n r w hw f hf x
  have hfin : {v : Pl K | finAt v (finEmb K n x) ∉ GLnLocal.integralGL (v.adicCompletion K) n}.Finite := by
    have hB : {v : Pl K | AdelicGLn.finiteRestrictedEquiv K n x v ∉
        GLnLocal.integralGL (v.adicCompletion K) n}.Finite :=
      Filter.eventually_cofinite.1 (AdelicGLn.finiteRestrictedEquiv K n x).2
    refine hB.subset ?_
    intro v hv
    have e : finAt v (finEmb K n x) = AdelicGLn.finiteRestrictedEquiv K n x v := by
      show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n x)).2) v = _
      rw [prodEquiv_finEmb]
    simpa [e] using hv
  set S : Finset (Pl K) := hfin.toFinset ∪ Finset.univ.image w with hS
  have hoff : ∀ v, v ∉ Set.range w → f v (finAt v (finEmb K n x)) =
      if finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n then 1 else 0 := by
    intro v hv
    rw [hf v hv]
    by_cases h : finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n
    · rw [if_pos h]; exact Set.indicator_of_mem (s := (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v))) h _
    · rw [if_neg h]; exact Set.indicator_of_notMem (s := (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v))) h _
  have hsupp : Function.mulSupport (fun v => f v (finAt v (finEmb K n x))) ⊆ (S : Set (Pl K)) := by
    intro v hv
    by_contra hvS
    have h1 : v ∉ Set.range w := by
      rintro ⟨i, rfl⟩
      exact hvS (by simp [hS])
    have h2 : finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
      by_contra h
      exact hvS (by simp only [hS, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset]; exact Or.inl h)
    exact hv ((hoff v h1).trans (if_pos h2))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  by_cases hx : x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))
  · rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul]
    have hsub : Finset.univ.image w ⊆ S := Finset.subset_union_right
    rw [← Finset.prod_subset hsub, Finset.prod_image (fun a _ b _ h => hw h)]
    intro v _ hv
    have h1 : v ∉ Set.range w := by
      rintro ⟨i, rfl⟩
      exact hv (by simp)
    rw [hoff v h1, if_pos (hx v h1)]
  · rw [Set.indicator_of_notMem hx, zero_mul]
    have hx' : ∃ v, v ∉ Set.range w ∧ finAt v (finEmb K n x) ∉ GLnLocal.integralGL (v.adicCompletion K) n := by
      by_contra hc
      push_neg at hc
      exact hx hc
    obtain ⟨v, h1, h2⟩ := hx'
    refine Finset.prod_eq_zero (i := v) ?_ ?_
    · simp only [hS, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl h2
    · rw [hoff v h1, if_neg h2]
