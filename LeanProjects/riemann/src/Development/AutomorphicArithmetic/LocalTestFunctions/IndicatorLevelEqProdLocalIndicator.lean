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

theorem UpperTheory.indicator_level_eq_prod_local_indicator :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K) (J : ∀ i, Subgroup (Gw n (w i))),
          (∀ i, J i ≤ GLnLocal.integralGL ((w i).adicCompletion K) n) → ∀ U : Set (AdelicGLn.FiniteAdelicGL K n),
          (∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i) → ∀ x,
          U.indicator (1 : AdelicGLn.FiniteAdelicGL K n → ℂ) x =
            ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator 1 x *
              ∏ i, (J i : Set (Gw n (w i))).indicator 1 (finAt (w i) (finEmb K n x)) := by
  intro K _ _ n r w J hJ U hU x
  have key : ∀ (h : AdelicGLn.FiniteAdelicGL K n) (v : Pl K),
      finAt v (finEmb K n h) = AdelicGLn.finiteRestrictedEquiv K n h v := by
    intro h v
    show AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n h)).2 v = _
    rw [prodEquiv_finEmb]
  have hint : ∀ h : AdelicGLn.FiniteAdelicGL K n, h ∈ AdelicGLn.integralFiniteGL K n ↔
      ∀ v : Pl K, finAt v (finEmb K n h) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
    intro h
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    simp only [key]
  by_cases hx : x ∈ U
  · obtain ⟨h1, h2⟩ := (hU x).1 hx
    have hy : x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈
        GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)) :=
      fun v _ => (hint x).1 h1 v
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Finset.prod_eq_one]
    · simp
    · intro i _
      rw [Set.indicator_of_mem (SetLike.mem_coe.2 (h2 i))]
      rfl
  · rw [Set.indicator_of_notMem hx]
    by_cases hJx : ∀ i, finAt (w i) (finEmb K n x) ∈ J i
    · have hy : x ∉ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈
          GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)) := by
        intro hy
        refine hx ((hU x).2 ⟨(hint x).2 fun v => ?_, hJx⟩)
        by_cases hv : v ∈ Set.range w
        · obtain ⟨i, rfl⟩ := hv
          exact hJ i (hJx i)
        · exact hy v hv
      rw [Set.indicator_of_notMem hy, zero_mul]
    · push_neg at hJx
      obtain ⟨i, hi⟩ := hJx
      rw [Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem (SetLike.mem_coe.not.2 hi) _), mul_zero]
