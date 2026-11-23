import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.prjFix :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
      IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) → IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) →
      ∃ e : TF K n, (∀ h, e h = (U : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (fun _ => ((m.real U : ℝ) : ℂ)⁻¹) h) ∧ Ofin μ m e = prj (fixF μ U) := by
  intro K _ _ n μ _ m _ U hUo hUc
  have hcl : IsClopen (U : Set (AdelicGLn.FiniteAdelicGL K n)) := ⟨U.isClosed_of_isOpen hUo, hUo⟩
  have hpos : (m.real U : ℝ) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(hUo.measure_pos m ⟨1, U.one_mem⟩).ne', hUc.measure_lt_top.ne⟩
  obtain ⟨-, hmem, a1, a2, a3, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U
  let e : TF K n := ⟨⟨(U : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (fun _ => ((m.real U : ℝ) : ℂ)⁻¹),
    hcl.continuous_indicator continuous_const⟩,
    HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx (fun _ => ((m.real U : ℝ) : ℂ)⁻¹)⟩
  have he : ∀ h, e h = (U : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (fun _ => ((m.real U : ℝ) : ℂ)⁻¹) h :=
    fun _ => rfl
  refine ⟨e, he, ContinuousLinearMap.ext fun v => ?_⟩
  have hO : Ofin μ m e v = ∫ h, e h • rhoF μ h v ∂m := by
    unfold Ofin
    rw [UnitaryRep.integrated_ccToL1_apply]
    rfl
  have hint : Integrable (fun h => e h • rhoF μ h v) m :=
    (e.continuous.smul (((rightRegularRep (rationalGLOne K n) μ).continuous_orbit v).comp
      MultiplicityOne.continuous_finProj)).integrable_of_hasCompactSupport e.hasCompactSupport.smul_right
  have h1 : Ofin μ m e v ∈ fixF μ U := by
    rw [hmem]
    intro u hu
    rw [hO, ← ContinuousLinearMap.integral_comp_comm _ hint,
      ← integral_mul_left_eq_self (fun h => e h • rhoF μ h v) u]
    congr 1
    funext h
    have : e (u * h) = e h := by
      rw [he, he]
      by_cases hh : h ∈ U
      · rw [Set.indicator_of_mem (show u * h ∈ (U : Set _) from U.mul_mem hu hh), Set.indicator_of_mem (show h ∈ (U : Set _) from hh)]
      · rw [Set.indicator_of_notMem (show u * h ∉ (U : Set _) from fun h' => hh ((U.mul_mem_cancel_left hu).1 h')),
          Set.indicator_of_notMem (show h ∉ (U : Set _) from hh)]
    rw [this, hmul, map_smul, ContinuousLinearMap.comp_apply]
  rw [← a2 _ h1, hO, ← ContinuousLinearMap.integral_comp_comm _ hint]
  have h2 : (fun h => prj (fixF μ U) (e h • rhoF μ h v)) = fun h => e h • prj (fixF μ U) v := by
    funext h
    rw [map_smul, he]
    by_cases hh : h ∈ U
    · rw [← ContinuousLinearMap.comp_apply, (a3 h hh).2]
    · rw [Set.indicator_of_notMem (show h ∉ (U : Set _) from hh), zero_smul, zero_smul]
  rw [h2, integral_smul_const]
  simp only [he]
  rw [integral_indicator_const _ hUo.measurableSet, Complex.real_smul, mul_inv_cancel₀ (by exact_mod_cast hpos), one_smul]
