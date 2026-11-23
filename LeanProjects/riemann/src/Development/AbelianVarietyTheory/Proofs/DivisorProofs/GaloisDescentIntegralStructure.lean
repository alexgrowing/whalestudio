import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionAbelianDvr
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemilinTwist

variable {W K' : Type} [CommRing W] [CommRing K'] [Algebra W K']

noncomputable def restrictFun (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) : W :=
  Classical.choose (h x)

theorem algebraMap_restrictFun (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) :
    algebraMap W K' (restrictFun σ h x) = σ (algebraMap W K' x) :=
  (Classical.choose_spec (h x)).symm

noncomputable def restrictHom (hinj : Function.Injective (algebraMap W K')) (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) : W →+* W where
  toFun := restrictFun σ h
  map_one' := hinj (by simp only [algebraMap_restrictFun, map_one])
  map_mul' x y := hinj (by simp only [algebraMap_restrictFun, map_mul])
  map_zero' := hinj (by simp only [algebraMap_restrictFun, map_zero])
  map_add' x y := hinj (by simp only [algebraMap_restrictFun, map_add])

theorem algebraMap_restrictHom (hinj : Function.Injective (algebraMap W K')) (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) :
    σ (algebraMap W K' x) = algebraMap W K' (restrictHom hinj σ h x) :=
  (algebraMap_restrictFun σ h x).symm

theorem exists_semilinear_twist : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'] (σ : K' ≃ₐ[K] K'), (∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K')) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ A _ _ hA G _ hG e he
  have hinj : Function.Injective (algebraMap W K') := IsFractionRing.injective W K'
  let τ : W →+* W := restrictHom hinj (σ : K' →+* K') hσ
  have hτ : ∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x) :=
    algebraMap_restrictHom hinj (σ : K' →+* K') hσ
  have hsq : spMap (σ : K' →+* K') ≫ spMap (algebraMap W K') = spMap (algebraMap W K') ≫ spMap τ := by
    rw [← Spec.map_comp, ← Spec.map_comp]; congr 1; ext x; simpa using hτ x
  have hK : spMap (algebraMap K K') = spMap (σ : K' →+* K') ≫ spMap (algebraMap K K') := by
    rw [← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm
  let s := pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _)
    (spMap (σ : K' →+* K')) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm)
  have hs1 : s ≫ pullback.fst A.hom (spMap (algebraMap K K')) = pullback.fst A.hom (spMap (algebraMap K K')) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hs2 : s ≫ pullback.snd A.hom (spMap (algebraMap K K')) =
      pullback.snd A.hom (spMap (algebraMap K K')) ≫ spMap (σ : K' →+* K') :=
    pullback.lift_snd _ _ _
  have hA1 := isGrpPullback_pullback A (spMap (algebraMap K K'))
  have hAs : IsGrpPullback ((Over.pullback (spMap (algebraMap K K'))).obj A)
      ((Over.pullback (spMap (algebraMap K K'))).obj A) (spMap (σ : K' →+* K')) s :=
    IsGrpPullback.cancel hA1 (hA1.congr hK hs1.symm) hs2
  haveI : IsMonHom e.hom := he
  have he1 := isGrpPullback_of_iso e
  haveI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have he2 := isGrpPullback_of_iso e.symm
  have hG1 := isGrpPullback_pullback G (spMap (algebraMap W K'))
  have h1 := (((he1.comp hAs).comp he2).comp hG1).congr
    (by rw [Category.id_comp, Category.comp_id, hsq]) rfl
  have hGτ := isGrpPullback_pullback G (spMap τ)
  have hGτK := isGrpPullback_pullback ((Over.pullback (spMap τ)).obj G) (spMap (algebraMap W K'))
  obtain ⟨e', he', he'φ⟩ := grpPullback_iso h1 (hGτK.comp hGτ)
  obtain ⟨F, hF, -⟩ := GlobalTheory.AbHomExtDvr.existsUnique_hom_extension_abelian_dvr W K' G
    ((Over.pullback (spMap τ)).obj G) hG (isAbelianScheme_pullback_obj _ G hG) e'.hom he'
  refine ⟨τ, F.left ≫ pullback.fst G.hom (spMap τ), hτ, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ spMap τ) (Over.w F)
  · have hFl : ((Over.pullback (spMap (algebraMap W K'))).map F).left ≫
        pullback.fst ((Over.pullback (spMap τ)).obj G).hom (spMap (algebraMap W K')) =
        pullback.fst G.hom (spMap (algebraMap W K')) ≫ F.left := pullback.lift_fst _ _ _
    rw [hF] at hFl
    rw [← Category.assoc, ← hFl, Category.assoc, he'φ]
    simp only [Category.assoc, Iso.symm_hom]
    rfl

end GlobalTheory.SemilinTwist
