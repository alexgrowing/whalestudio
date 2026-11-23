import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private theorem out_eq_cuspQuot {E : Type} [Field E] [NumberField E] {r : ℕ}
    (F : AdelicGLn.AdelicGL E r → ℂ) (h : AutomorphicForm.IsLeftInvariant F)
    (y : RightCosetSpace (rationalGLOne E r)) :
    F ((Quotient.out y : normOneGL E r) : AdelicGLn.AdelicGL E r) = CuspidalSpectrum.cuspQuot h y := by
  have e : RightCosetSpace.mk (rationalGLOne E r) (Quotient.out y) = y := Quotient.out_eq y
  calc F ((Quotient.out y : normOneGL E r) : AdelicGLn.AdelicGL E r)
      = CuspidalSpectrum.cuspQuot h (RightCosetSpace.mk (rationalGLOne E r) (Quotient.out y)) := rfl
    _ = CuspidalSpectrum.cuspQuot h y := by rw [e]

theorem UpperTheory.integrable_translate_mul_conj_and_inner_self_ne_zero :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (S : Set (Pl E)) (r : ℕ) (b : Blo S r),
      (∀ g : GA E r, Integrable (fun y : RightCosetSpace (rationalGLOne E r) => b.f.1 (((Quotient.out y : normOneGL E r) : GA E r) * g) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r))) (quotientMeasure (rationalGLOne E r) (mu1 E r))) ∧
      ∫ y : RightCosetSpace (rationalGLOne E r), b.f.1 ((Quotient.out y : normOneGL E r) : GA E r) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r)) ∂(quotientMeasure (rationalGLOne E r) (mu1 E r)) ≠ 0 := by
  intro E _ _ _ S r b
  have hfin := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
  have hcont : Continuous b.f.1 := b.cusp.1.continuous
  have hL : AutomorphicForm.IsLeftInvariant b.f.1 := b.cusp.1.isLeftInvariant
  obtain ⟨C, hC⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms b.cusp
  have hsec : ∀ s : {x : ℝ // 0 < x}, centralSection E r s = zt E r (Real.log s.1) := fun s => by
    unfold zt
    exact congrArg _ (Subtype.ext (Real.exp_log s.2).symm)
  have hb : ∀ g, ‖b.f.1 g‖ ≤ C := fun g => by
    obtain ⟨s, y, hy, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL g
    rw [hsec s, b.cen]
    exact hC y hy
  have hbq : ∀ (F : AdelicGLn.AdelicGL E r → ℂ) (h : AutomorphicForm.IsLeftInvariant F), (∀ g, ‖F g‖ ≤ C) →
      ∀ q, ‖CuspidalSpectrum.cuspQuot h q‖ ≤ C := fun F h hF q => by
    rw [← out_eq_cuspQuot F h q]
    exact hF _
  have hq := CuspidalSpectrum.continuous_cuspQuot hL hcont
  refine ⟨fun g => ?_, fun h0 => ?_⟩
  · have hLg : AutomorphicForm.IsLeftInvariant (fun x => b.f.1 (x * g)) := fun γ x => by
      show b.f.1 (_ * x * g) = b.f.1 (x * g)
      rw [mul_assoc]
      exact hL γ _
    have hcg : Continuous (fun x : AdelicGLn.AdelicGL E r => b.f.1 (x * g)) :=
      hcont.comp (continuous_id.mul continuous_const)
    have hqg := CuspidalSpectrum.continuous_cuspQuot hLg hcg
    have e : (fun y : RightCosetSpace (rationalGLOne E r) => b.f.1 (((Quotient.out y : normOneGL E r) : GA E r) * g) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r))) =
        fun y => CuspidalSpectrum.cuspQuot hLg y * starRingEnd ℂ (CuspidalSpectrum.cuspQuot hL y) := by
      funext y
      rw [← out_eq_cuspQuot _ hLg y, ← out_eq_cuspQuot _ hL y]
    rw [e]
    refine Integrable.of_bound (hqg.mul (Complex.continuous_conj.comp hq)).aestronglyMeasurable (C * C)
      (Filter.Eventually.of_forall fun q => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hbq _ hLg (fun x => hb _) q) (hbq _ hL hb q) (norm_nonneg _)
      ((norm_nonneg _).trans (hbq _ hL hb q))
  · have e : ∀ y : RightCosetSpace (rationalGLOne E r),
        b.f.1 ((Quotient.out y : normOneGL E r) : GA E r) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r)) =
        ((‖CuspidalSpectrum.cuspQuot hL y‖ ^ 2 : ℝ) : ℂ) := fun y => by
      rw [out_eq_cuspQuot _ hL y, Complex.mul_conj', Complex.ofReal_pow]
    have h1 : ∫ q, ‖CuspidalSpectrum.cuspQuot hL q‖ ^ 2 ∂(quotientMeasure (rationalGLOne E r) (mu1 E r)) = 0 := by
      rw [← Complex.ofReal_eq_zero, ← integral_complex_ofReal, ← h0]
      exact integral_congr_ae (Filter.Eventually.of_forall fun q => (e q).symm)
    have hi : Integrable (fun q => ‖CuspidalSpectrum.cuspQuot hL q‖ ^ 2) (quotientMeasure (rationalGLOne E r) (mu1 E r)) :=
      Integrable.of_bound (hq.norm.pow 2).aestronglyMeasurable (C ^ 2) (Filter.Eventually.of_forall fun q => by
        rw [norm_pow, norm_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbq _ hL hb q) 2)
    have h2 := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg _) hi).1 h1
    have h3 := (RightCosetSpace.quasiMeasurePreserving_mk (rationalGLOne E r) (mu1 E r)).ae_eq h2
    have h4 := (Continuous.ae_eq_iff_eq (mu1 E r) (f := fun y : normOneGL E r => ‖b.f.1 (y : AdelicGLn.AdelicGL E r)‖ ^ 2)
      ((hcont.comp continuous_subtype_val).norm.pow 2) continuous_const).1 h3
    apply b.ne
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨s, y, hy, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL g
    rw [hsec s, b.cen]
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (congrFun h4 ⟨y, hy⟩))
