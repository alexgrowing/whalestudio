import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem conv_left {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (f : GA E n → ℂ)
    (α : Lie E n → ℂ) (z : GA E n) (h : ∀ g, f (z * g) = f g) (g : GA E n) : Af.StrongMultiplicityOne.conv f α (z * g) = Af.StrongMultiplicityOne.conv f α g := by
  have e : chart f (z * g) = chart f g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, h]
    · rfl
  unfold Af.StrongMultiplicityOne.conv
  rw [e]

private theorem zero_of_sq {E : Type} [Field E] [NumberField E] {n : ℕ} (μ : Measure (Reduction.normOneGL E n))
    [μ.IsHaarMeasure] (F : AdelicGLn.AdelicGL E n → ℂ) (hc : Continuous F) (C : ℝ) (hC : ∀ g, ‖F g‖ ≤ C)
    (h : IsLeftInvariant F)
    (h0 : ∫ q, starRingEnd ℂ (CuspidalSpectrum.cuspQuot h q) * CuspidalSpectrum.cuspQuot h q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne E n) μ) = 0) :
    ∀ y ∈ Reduction.normOneGL E n, F y = 0 := by
  have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
  have hq := CuspidalSpectrum.continuous_cuspQuot h hc
  have hb : ∀ q, ‖CuspidalSpectrum.cuspQuot h q‖ ≤ C := fun q => by
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    exact hC _
  have h1 : ∫ q, ‖CuspidalSpectrum.cuspQuot h q‖ ^ 2
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne E n) μ) = 0 := by
    rw [← Complex.ofReal_eq_zero, ← integral_complex_ofReal, ← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [Complex.conj_mul', Complex.ofReal_pow]
  have hi : Integrable (fun q => ‖CuspidalSpectrum.cuspQuot h q‖ ^ 2)
      (RightCosetSpace.quotientMeasure (Reduction.rationalGLOne E n) μ) :=
    Integrable.of_bound (hq.norm.pow 2).aestronglyMeasurable (C ^ 2) (Filter.Eventually.of_forall fun q => by
      rw [norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb q) 2)
  have h2 := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg _) hi).1 h1
  have h3 := (RightCosetSpace.quasiMeasurePreserving_mk (Reduction.rationalGLOne E n) μ).ae_eq h2
  have h4 := (Continuous.ae_eq_iff_eq μ (f := fun y : Reduction.normOneGL E n => ‖F y‖ ^ 2)
    ((hc.comp continuous_subtype_val).norm.pow 2) continuous_const).1 h3
  intro y hy
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (congrFun h4 ⟨y, hy⟩))

theorem UpperTheory.V.Af.StrongMultiplicityOne.orthConv :
    UpperTheory.V.Af.StrongMultiplicityOne.OrthStep → UpperTheory.V.Af.StrongMultiplicityOne.ConvCont → UpperTheory.V.Af.StrongMultiplicityOne.OrthConv := by
  intro hS hC E _ _ _ n μ _ φ φ' hφ hφ' ho β β' e
  obtain ⟨C, hb⟩ := exists_norm_le_of_mem_centralCuspForms hφ
  obtain ⟨C', hb'⟩ := exists_norm_le_of_mem_centralCuspForms hφ'
  have l : IsLeftInvariant (Af.StrongMultiplicityOne.conv φ.1 β) := fun γ g => conv_left _ _ _ (φ.2.1.isLeftInvariant γ) g
  have l' : IsLeftInvariant (Af.StrongMultiplicityOne.conv φ'.1 β') := fun γ g => conv_left _ _ _ (φ'.2.1.isLeftInvariant γ) g
  obtain ⟨hc, D, hD⟩ := hC E n φ'.1 φ'.2.1.continuous ⟨C', hb'⟩ β'
  have s1 : ∀ g, ∫ q, starRingEnd ℂ (quotTr φ g q) * CuspidalSpectrum.cuspQuot l' q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne E n) μ) = 0 := fun g =>
    hS E n μ φ'.1 φ'.2.1.continuous ⟨C', hb'⟩ φ'.2.1.isLeftInvariant (fun q => starRingEnd ℂ (quotTr φ g q))
      (Complex.continuous_conj.comp (continuous_quotTr φ g))
      ⟨C, fun q => by
        obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
        rw [Complex.norm_conj]
        exact hb _⟩
      (fun g' _ => ho g g') β' l'
  have s2 := hS E n μ φ.1 φ.2.1.continuous ⟨C, hb⟩ φ.2.1.isLeftInvariant
    (fun q => starRingEnd ℂ (CuspidalSpectrum.cuspQuot l' q))
    (Complex.continuous_conj.comp (CuspidalSpectrum.continuous_cuspQuot l' hc))
    ⟨D, fun q => by
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      rw [Complex.norm_conj]
      exact hD _⟩
    (fun g _ => by
      have h := congrArg (starRingEnd ℂ) (s1 g)
      rw [← integral_conj, map_zero] at h
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)) h
      simp only [map_mul, Complex.conj_conj]
      exact mul_comm _ _) β l
  have e' : CuspidalSpectrum.cuspQuot l = CuspidalSpectrum.cuspQuot l' :=
    CuspidalSpectrum.cuspQuot_surj_eq l l' fun y => congrFun e _
  rw [e'] at s2
  have z := zero_of_sq μ _ hc D hD l' s2
  rw [e]
  funext x
  obtain ⟨s, y, hy, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL x
  exact (conv_left _ _ _ (hφ' s) y).trans (z y hy)
