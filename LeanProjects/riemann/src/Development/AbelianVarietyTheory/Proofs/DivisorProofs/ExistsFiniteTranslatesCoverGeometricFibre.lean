import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteCoverByTranslatePairsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GroupLawsOnCoverAgreeOnCommonPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreCover

theorem cover_geometric_fibre : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (K : Type) [Field K] [IsAlgClosed K] (ξ : Sp K ⟶ S), (∀ z, ∃ x ∈ V, A.hom x = ξ z) → ∃ (n : ℕ) (a : Fin n → (Over.mk ξ ⟶ A)), ⨆ i, ((fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  intro S A _ hA V K _ _ ξ hcov
  have hA' : IsAbelianScheme ((Over.pullback ξ).obj A) := GlobalTheory.isAbelianScheme_pullback_obj ξ A hA
  have hpb := isGrpPullback_pullback A ξ
  have hne : ((pullback.fst A.hom ξ ⁻¹ᵁ V : ((Over.pullback ξ).obj A).left.Opens) : Set ((Over.pullback ξ).obj A).left).Nonempty := by
    obtain ⟨x, hxV, hx⟩ := hcov (default : PrimeSpectrum K)
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback hpb.1 x _ hx
    exact ⟨p, by show pullback.fst A.hom ξ p ∈ V; rw [hp]; exact hxV⟩
  obtain ⟨n, a', ha'⟩ := GlobalTheory.T.abelianVariety_finite_cover_by_translate_pairs K ((Over.pullback ξ).obj A) hA' (pullback.fst A.hom ξ ⁻¹ᵁ V) hne
  let a : Fin n → (Over.mk ξ ⟶ A) := fun i => Over.homMk ((a' i).left ≫ pullback.fst A.hom ξ) (by
    show ((a' i).left ≫ pullback.fst A.hom ξ) ≫ A.hom = ξ
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have h := Over.w (a' i)
    change (a' i).left ≫ pullback.snd A.hom ξ = 𝟙 _ at h
    rw [h, Category.id_comp])
  refine ⟨n, a, ?_⟩
  have e : (A ⊗ Over.mk ξ).hom = ((Over.pullback ξ).obj A).hom ≫ ξ := by
    first | rfl | exact pullback.condition
  have hx : (fst A (Over.mk ξ)).left = Over.Hom.left (𝟙 ((Over.pullback ξ).obj A)) ≫ pullback.fst A.hom ξ := by
    first | rfl | simp
  have hy : ∀ i, (snd A (Over.mk ξ) ≫ a i).left = (toUnit ((Over.pullback ξ).obj A) ≫ a' i).left ≫ pullback.fst A.hom ξ := by
    intro i; first | rfl | simp [a]
  have key₁ : ∀ i, (fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)).left =
      (𝟙 ((Over.pullback ξ).obj A) * (toUnit ((Over.pullback ξ).obj A) ≫ a' i)).left ≫ pullback.fst A.hom ξ := fun i =>
    GlobalTheory.CoverOpCompat.push_mul hpb (T := ((Over.pullback ξ).obj A).left) (ρ := ((Over.pullback ξ).obj A).hom)
      (r := (A ⊗ Over.mk ξ).hom) e (𝟙 ((Over.pullback ξ).obj A)) (toUnit ((Over.pullback ξ).obj A) ≫ a' i)
      (fst A (Over.mk ξ)) (snd A (Over.mk ξ) ≫ a i) hx (hy i)
  have key₂ : ∀ i, ((snd A (Over.mk ξ) ≫ a i)⁻¹).left =
      ((toUnit ((Over.pullback ξ).obj A) ≫ a' i)⁻¹).left ≫ pullback.fst A.hom ξ := fun i =>
    GlobalTheory.CoverOpCompat.push_inv hpb (T := ((Over.pullback ξ).obj A).left) (ρ := ((Over.pullback ξ).obj A).hom)
      (r := (A ⊗ Over.mk ξ).hom) e (toUnit ((Over.pullback ξ).obj A) ≫ a' i) (snd A (Over.mk ξ) ≫ a i) (hy i)
  have key₃ : ∀ i, (fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)⁻¹).left =
      (𝟙 ((Over.pullback ξ).obj A) * (toUnit ((Over.pullback ξ).obj A) ≫ a' i)⁻¹).left ≫ pullback.fst A.hom ξ := fun i =>
    GlobalTheory.CoverOpCompat.push_mul hpb (T := ((Over.pullback ξ).obj A).left) (ρ := ((Over.pullback ξ).obj A).hom)
      (r := (A ⊗ Over.mk ξ).hom) e (𝟙 ((Over.pullback ξ).obj A)) ((toUnit ((Over.pullback ξ).obj A) ≫ a' i)⁻¹)
      (fst A (Over.mk ξ)) ((snd A (Over.mk ξ) ≫ a i)⁻¹) hx (key₂ i)
  refine Eq.trans ?_ ha'
  congr 1
  funext i
  rw [key₁ i, key₃ i, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]

end GlobalTheory.FibreCover
