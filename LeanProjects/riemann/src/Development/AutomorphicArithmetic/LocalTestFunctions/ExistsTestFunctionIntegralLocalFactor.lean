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

theorem UpperTheory.exists_testFunction_integral_local_factor :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (mw : Measure (Gw n w)) [mw.IsHaarMeasure] (J : Subgroup (Gw n w)), CO J →
          ∀ (ψ : CompactlySupportedContinuousMap (Gw n w) ℂ), (∀ k ∈ J, ∀ x, ψ (x * k) = ψ x) →
          ∀ (R : AdelicGLn.FiniteAdelicGL K n → ℂ), (∀ y x, R (AdelicGLn.localEmbedding w y * x) = R x) →
          ∀ e₀ : TF K n, (∀ x, e₀ x = R x * (J : Set (Gw n w)).indicator 1 (finAt w (finEmb K n x))) →
          ∃ g : TF K n, (∀ x, g x = (mw.real J : ℂ) * (R x * ψ (finAt w (finEmb K n x)))) ∧
            (∫ x, g x ∂m = (∫ y, ψ y ∂mw) * ∫ x, e₀ x ∂m) ∧
            ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (AdelicGLn.FiniteAdelicGL K n) H),
              π.integrated m (UnitaryRep.ccToL1 m g) =
                (π.compHom (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1).integrated mw (UnitaryRep.ccToL1 mw ψ) ∘L
                  π.integrated m (UnitaryRep.ccToL1 m e₀) := by
  intro K _ _ n m _ w _ _ mw _ J hJ ψ hψ R hR e₀ he₀
  have hp := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1
  obtain ⟨g, hg, -, hop⟩ := UpperTheory.ConvolutionTheory.Tf.homConv _ _ (AdelicGLn.localEmbedding w) hp m mw ψ e₀
  have hJm : MeasurableSet (J : Set (Gw n w)) := hJ.2.measurableSet
  have hval : ∀ x, g x = (mw.real J : ℂ) * (R x * ψ (finAt w (finEmb K n x))) := by
    intro x
    set a := finAt w (finEmb K n x) with ha
    have hfa : ∀ y, finAt w (finEmb K n ((AdelicGLn.localEmbedding w y)⁻¹ * x)) = y⁻¹ * a := by
      intro y
      rw [map_mul, finAt_mul, map_inv, finAt_inv, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1]
    have hRy : ∀ y, R ((AdelicGLn.localEmbedding w y)⁻¹ * x) = R x := by
      intro y
      rw [← map_inv, hR]
    have hpt : ∀ y, ψ (a * y) * e₀ ((AdelicGLn.localEmbedding w (a * y))⁻¹ * x) =
        (J : Set (Gw n w)).indicator (fun _ => R x * ψ a) y := by
      intro y
      rw [he₀, hRy, hfa]
      have e1 : (a * y)⁻¹ * a = y⁻¹ := by group
      rw [e1]
      by_cases hy : y ∈ J
      · have hy' : y⁻¹ ∈ J := J.inv_mem hy
        rw [Set.indicator_of_mem (show y⁻¹ ∈ (J : Set (Gw n w)) from hy'),
          Set.indicator_of_mem (show y ∈ (J : Set (Gw n w)) from hy), hψ y hy, Pi.one_apply]
        ring
      · have hy' : y⁻¹ ∉ J := fun h => hy (by simpa using J.inv_mem h)
        rw [Set.indicator_of_notMem (show y⁻¹ ∉ (J : Set (Gw n w)) from hy'),
          Set.indicator_of_notMem (show y ∉ (J : Set (Gw n w)) from hy)]
        ring
    rw [hg, ← integral_mul_left_eq_self _ a]
    simp only [hpt]
    rw [integral_indicator hJm, setIntegral_const]
    simp [Measure.real, mul_comm]
  have hint : ∫ x, g x ∂m = (∫ y, ψ y ∂mw) * ∫ x, e₀ x ∂m := by
    have hf : IsCompact (tsupport ψ) := ψ.hasCompactSupport.isCompact
    have hS : IsCompact ((AdelicGLn.localEmbedding w) '' tsupport ψ * tsupport e₀) :=
      (hf.image hp).mul e₀.hasCompactSupport.isCompact
    have hker : Continuous fun q : AdelicGLn.FiniteAdelicGL K n × Gw n w =>
        ψ q.2 * e₀ ((AdelicGLn.localEmbedding w q.2)⁻¹ * q.1) :=
      (ψ.continuous.comp continuous_snd).mul
        (e₀.continuous.comp ((hp.comp continuous_snd).inv.mul continuous_fst))
    have hI : Integrable (Function.uncurry fun (x : AdelicGLn.FiniteAdelicGL K n) (y : Gw n w) =>
        ψ y * e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x)) (m.prod mw) := by
      refine Continuous.integrable_of_hasCompactSupport hker ?_
      refine HasCompactSupport.intro (hS.prod hf) fun q hq => ?_
      change ψ q.2 * e₀ ((AdelicGLn.localEmbedding w q.2)⁻¹ * q.1) = 0
      by_contra hne
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
      exact hq ⟨⟨_, ⟨q.2, subset_tsupport _ h1, rfl⟩, _, subset_tsupport _ h2,
        mul_inv_cancel_left _ _⟩, subset_tsupport _ h1⟩
    simp only [hg]
    rw [integral_integral_swap hI]
    simp only [integral_const_mul]
    have hinv : ∀ y : Gw n w, ∫ x, e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x) ∂m = ∫ x, e₀ x ∂m :=
      fun y => integral_mul_left_eq_self (fun x => e₀ x) _
    simp only [hinv]
    rw [integral_mul_const]
  exact ⟨g, hval, hint, hop⟩
