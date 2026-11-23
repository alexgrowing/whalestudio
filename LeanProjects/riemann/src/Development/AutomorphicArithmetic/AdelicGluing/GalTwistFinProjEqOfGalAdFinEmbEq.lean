import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalAdEq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdNormOne
import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem galAd_adeleMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (a : NumberField.AdeleRing (𝓞 F) F) :
    galAd σ (AdeleBaseChange.adeleMap F E a) = AdeleBaseChange.adeleMap F E a := by
  change AdeleBaseChange.adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
    ((AdeleBaseChange.adeleTensorEquiv F E).symm (AdeleBaseChange.adeleMap F E a))) = _
  rw [AdeleBaseChange.adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul,
    AdeleBaseChange.adeleTensorEquiv_tmul, map_one, map_one, one_mul]
  rfl

private theorem exists_pow_eq (d : ℕ) (hd : d ≠ 0) (t : {r : ℝ // 0 < r}) :
    ∃ s : {r : ℝ // 0 < r}, s ^ d = t := by
  refine ⟨rpowHom ((d : ℝ))⁻¹ t, Subtype.ext ?_⟩
  change ((t : ℝ) ^ ((d : ℝ))⁻¹) ^ d = t
  exact Real.rpow_inv_natCast_pow t.2.le hd

private theorem map_centralSection {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (n : ℕ) (t : {r : ℝ // 0 < r}) :
    (mapGL n (galAd σ) (centralSection E n t) : AdelicGLn.AdelicGL E n) = centralSection E n t := by
  obtain ⟨s, rfl⟩ := exists_pow_eq (Module.finrank F E) Module.finrank_pos.ne' t
  have h := UpperTheory.centralSection_baseChange F E n s
  rw [← h]
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact galAd_adeleMap σ _

theorem UpperTheory.galTwist_finProj_eq_of_galAd_finEmb_eq :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n →
          ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ h h' : AdelicGLn.FiniteAdelicGL E n,
            (mapGL n (galAd σ) (finEmb E n h) : AdelicGLn.AdelicGL E n) = finEmb E n h' →
            θ.e (MultiplicityOne.finProj E n h) = MultiplicityOne.finProj E n h' := by
  intro F E _ _ _ _ _ _ σ n hn μ _ θ hθ h h' hh
  refine Subtype.ext ?_
  rw [hθ, MultiplicityOne.coe_finProj, MultiplicityOne.coe_finProj, map_mul, map_inv, hh, map_centralSection]
  set s := detModule E n (finEmb E n h) with hs
  have hmem : finEmb E n h' * (centralSection E n s)⁻¹ ∈ normOneGL E n := by
    have h1 := (θ.e (MultiplicityOne.finProj E n h)).2
    rw [hθ, MultiplicityOne.coe_finProj, map_mul, map_inv, hh, map_centralSection] at h1
    exact h1
  have hd : detModule E n (finEmb E n h') = s := by
    have h2 := (mem_normOneGL_iff_detModule).1 hmem
    rw [map_mul, map_inv, detModule_centralSection hn] at h2
    exact mul_inv_eq_one.1 h2
  rw [hd]
