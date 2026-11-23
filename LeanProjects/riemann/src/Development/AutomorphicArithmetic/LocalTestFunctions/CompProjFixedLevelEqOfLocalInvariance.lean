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

private theorem level_decomp (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (r : ℕ) (w : Fin r → Pl K) (hw : Function.Injective w) (J : ∀ i, Subgroup (Gw n (w i)))
    (A : LL μ →L[ℂ] LL μ) (hA : ∀ i, ∀ k ∈ J i, A ∘L rhoL μ (w i) k = A)
    (g : AdelicGLn.FiniteAdelicGL K n) (hg : ∀ i, finAt (w i) (finEmb K n g) ∈ J i) (S : Finset (Fin r)) :
    ∃ a : AdelicGLn.FiniteAdelicGL K n, A ∘L rhoF μ a = A ∧
      (∀ i ∈ S, finAt (w i) (finEmb K n a) = finAt (w i) (finEmb K n g)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), (∀ i ∈ S, v ≠ w i) → finAt v (finEmb K n a) = 1 := by
  classical
  obtain ⟨-, -, -, -, -, hmul, hone, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have e : ∀ (u : HeightOneSpectrum (𝓞 K)) (y : AdelicGLn.FiniteAdelicGL K n),
      finAt u (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y u := fun _ _ => rfl
  have emul : ∀ (u : HeightOneSpectrum (𝓞 K)) (y z : AdelicGLn.FiniteAdelicGL K n),
      finAt u (finEmb K n (y * z)) = finAt u (finEmb K n y) * finAt u (finEmb K n z) := by
    intro u y z
    rw [e, e, e, map_mul, RestrictedProduct.mul_apply]
  have eone : ∀ u : HeightOneSpectrum (𝓞 K), finAt u (finEmb K n 1) = 1 := by
    intro u
    rw [e, map_one, RestrictedProduct.one_apply]
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, ?_, by simp, fun v _ => eone v⟩
    rw [hone]
    exact ContinuousLinearMap.comp_id A
  | insert i S hi ih =>
    obtain ⟨a, h1, h2, h3⟩ := ih
    obtain ⟨-, l2, l3, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)
    refine ⟨a * AdelicGLn.localEmbedding (w i) (finAt (w i) (finEmb K n g)), ?_, ?_, ?_⟩
    · rw [hmul, ← ContinuousLinearMap.comp_assoc, h1]
      exact hA i _ (hg i)
    · intro j hj
      rw [emul]
      rcases Finset.mem_insert.1 hj with rfl | hj
      · rw [l2, h3 _ (fun k hk e => hi (by rw [hw e]; exact hk)), one_mul]
      · have hne : w j ≠ w i := fun e => hi (hw e ▸ hj)
        rw [l3 _ hne, mul_one, h2 j hj]
    · intro v hv
      rw [emul, h3 v (fun j hj => hv j (Finset.mem_insert_of_mem hj)),
        l3 v (hv i (Finset.mem_insert_self _ _)), one_mul]

theorem UpperTheory.comp_proj_fixed_level_eq_of_local_invariance :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
          (r : ℕ) (w : Fin r → Pl K), Function.Injective w → ∀ (J : ∀ i, Subgroup (Gw n (w i))) (U US : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
          IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) → IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) →
          (∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i) →
          (∀ h, h ∈ US ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) = 1) →
          ∀ A : LL μ →L[ℂ] LL μ, (∀ i, ∀ k ∈ J i, A ∘L rhoL μ (w i) k = A) → A ∘L prj (fixF μ U) = A ∘L prj (fixF μ US) := by
  intro K _ _ n μ _ m _ r w hw J U US hUo hUc hU hUS A hA
  obtain ⟨-, hmemU, -, -, -, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U
  obtain ⟨-, hmemS, b1, -, -, -, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ US
  have hle : fixF μ U ≤ fixF μ US := fun v hv => (hmemS v).2 fun u hu =>
    (hmemU v).1 hv u ((hU u).2 ⟨((hUS u).1 hu).1, fun i => by
      rw [((hUS u).1 hu).2 i]
      exact (J i).one_mem⟩)
  have hPQ : prj (fixF μ U) ∘L prj (fixF μ US) = prj (fixF μ U) := by
    unfold prj
    exact Submodule.starProjection_comp_starProjection_of_le (Submodule.topologicalClosure_mono hle)
  have hpt : ∀ g ∈ U, ∀ x ∈ fixF μ US, A (rhoF μ g x) = A x := by
    intro g hg x hx
    obtain ⟨hgi, hgJ⟩ := (hU g).1 hg
    obtain ⟨a, h1, h2, h3⟩ := level_decomp K n μ r w hw J A hA g hgJ Finset.univ
    have e : ∀ (u : HeightOneSpectrum (𝓞 K)) (y : AdelicGLn.FiniteAdelicGL K n),
        finAt u (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y u := fun _ _ => rfl
    have ec : ∀ u : HeightOneSpectrum (𝓞 K), finAt u (finEmb K n (a⁻¹ * g)) =
        (finAt u (finEmb K n a))⁻¹ * finAt u (finEmb K n g) := by
      intro u
      rw [e, e, e, map_mul, map_inv]
      rfl
    have hcomp : ∀ i, finAt (w i) (finEmb K n (a⁻¹ * g)) = 1 := by
      intro i
      rw [ec, h2 i (Finset.mem_univ i), inv_mul_cancel]
    have hb : a⁻¹ * g ∈ US := by
      refine (hUS _).2 ⟨(AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 fun v => ?_, hcomp⟩
      rw [← e]
      by_cases hv : ∃ i, v = w i
      · obtain ⟨i, rfl⟩ := hv
        rw [hcomp i]
        exact one_mem _
      · rw [ec, h3 v (fun i _ h => hv ⟨i, h⟩), inv_one, one_mul, e]
        exact (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 hgi v
    have hga : rhoF μ g x = rhoF μ a x := by
      have hg' : g = a * (a⁻¹ * g) := (mul_inv_cancel_left a g).symm
      rw [hg', hmul, ContinuousLinearMap.comp_apply, (hmemS x).1 hx _ hb]
    rw [hga, ← ContinuousLinearMap.comp_apply, h1]
  have hcl : ∀ x ∈ fixF μ US, A (prj (fixF μ U) x) = A x := by
    intro x hx
    obtain ⟨e, he, hOe⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m U hUo hUc
    have hpos : (m.real U : ℝ) ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(hUo.measure_pos m ⟨1, U.one_mem⟩).ne', hUc.measure_lt_top.ne⟩
    have hO : Ofin μ m e x = ∫ h, e h • rhoF μ h x ∂m := by
      unfold Ofin
      rw [UnitaryRep.integrated_ccToL1_apply]
      rfl
    have hint : Integrable (fun h => e h • rhoF μ h x) m :=
      (e.continuous.smul (((rightRegularRep (rationalGLOne K n) μ).continuous_orbit x).comp
        MultiplicityOne.continuous_finProj)).integrable_of_hasCompactSupport e.hasCompactSupport.smul_right
    rw [← hOe, hO, ← ContinuousLinearMap.integral_comp_comm _ hint]
    have h2 : (fun h => A (e h • rhoF μ h x)) = fun h => e h • A x := by
      funext h
      rw [map_smul, he]
      by_cases hh : h ∈ U
      · rw [hpt h hh x hx]
      · rw [Set.indicator_of_notMem (show h ∉ (U : Set _) from hh), zero_smul, zero_smul]
    rw [h2, integral_smul_const]
    simp only [he]
    rw [integral_indicator_const _ hUo.measurableSet, Complex.real_smul, mul_inv_cancel₀ (by exact_mod_cast hpos), one_smul]
  refine ContinuousLinearMap.ext fun v => ?_
  have hPv : prj (fixF μ U) v = prj (fixF μ U) (prj (fixF μ US) v) := by
    rw [← ContinuousLinearMap.comp_apply, hPQ]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hPv, hcl _ (b1 v)]
