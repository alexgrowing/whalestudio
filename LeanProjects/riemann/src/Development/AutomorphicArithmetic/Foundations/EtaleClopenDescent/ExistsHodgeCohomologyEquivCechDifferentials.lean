import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AutomorphicArithmetic.GenericGermInjectivity.GermInjRangePre
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsAffCoverProdCechOpen
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem UpperTheory.Cb.exists_hodge_cohomology_equiv_cech_differentials :
    ∃ e : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a b : ℕ), hodgeH p a b ≃ₗ[ℂ] (cech fun I => omB ℂ Z.functionField (B I) a).H b,
      (∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B)
        (d' : ℕ) (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [SmoothOfRelativeDimension d' p'] [inst' : Algebra ℂ Z'.functionField] (κ : Type) [LinearOrder κ] [Fintype κ] (U' : κ → Z'.Opens) (B' : Finset κ → Subalgebra ℂ Z'.functionField) (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' U' B')
        (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField) (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField) (τ : κ → ι),
        IsDRMap ℂ ψ φ → (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)), ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) → (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) →
        ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Z.functionField (B I) a) (cech fun I => omB ℂ Z'.functionField (B' I) a) (pullC τ φ)) (z : hodgeH p a b),
          e d' Z' p' κ U' B' hinst' hU' a b (hodgePull hf a b z) = Cx.hmap _ _ (pullC τ φ) hm b (e d Z p ι U B hinst hU a b z)) ∧
      (∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (Y : Scheme.{0}) [IsIntegral Y] (p' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d p'] [inst' : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (B' : Finset ι → Subalgebra ℂ Y.functionField) (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p') (hU : IsAffCover p U B) (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B'),
        (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) →
        ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Y.functionField (B' I) a) (cech fun I => omB ℂ Z.functionField (B I) a) (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s))) (z : hodgeH p' a b),
          e d Z p ι U B hinst hU a b (hodgeTrace hc a b z) = Cx.hmap _ _ (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s)) hm b (e d Y p' ι (fun i => c ⁻¹ᵁ U i) B' hinst' hU' a b z)) := by
  refine ⟨fun d Z _ p _ inst ι _ _ U B hinst hU a b => UpperTheory.GenericCoverClass.cmp d p hinst hU a b, ?_, ?_⟩
  · exact UpperTheory.isAffCover_prod_cechOpen
  · intro d Z _ p _ inst Y _ p' _ inst' _ _ c hc _ _ ι _ _ U B B' hinst hinst' hU hU' hg a b hm z
    exact UpperTheory.GenericCoverClass.cmp_trace d Z p Y p' c hc ι U B B' hinst hinst' hU hU' hg a b hm z
