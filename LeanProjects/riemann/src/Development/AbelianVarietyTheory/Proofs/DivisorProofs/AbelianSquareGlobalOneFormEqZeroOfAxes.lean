import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimOfAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsProjectiveRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1VanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesO1OfProjectiveRankCup
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh.AxesForm

open GlobalTheory.AbCoh.PrimForm

theorem eq_zero_of_axes : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ y : GlobForm (A ⊗ A).hom, GlobalTheory.AbCoh.pF (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 → GlobalTheory.AbCoh.pF (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0 := by
  intro R _ A _ g hA hg y h₁ h₂
  obtain ⟨hA2, hg2⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨f1, p1, r1⟩ := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hg
  obtain ⟨f2, p2, r2⟩ := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R (A ⊗ A) (g + g) hA2 hg2
  let N : GlobForm (A ⊗ A).hom →ₗ[R] GlobForm A.hom × GlobForm A.hom :=
    LinearMap.prod (pF (lift (𝟙 A) (toUnit A ≫ η[A]))) (pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
  let P : GlobForm A.hom × GlobForm A.hom →ₗ[R] GlobForm (A ⊗ A).hom :=
    LinearMap.coprod (pF (fst A A)) (pF (snd A A))
  have hNP : N ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
    · show pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) x.1 + pF (snd A A) x.2) = x.1
      rw [map_add, pF_comp, pF_comp, lift_fst, lift_snd, pF_id, pF_unit, add_zero]
    · show pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) x.1 + pF (snd A A) x.2) = x.2
      rw [map_add, pF_comp, pF_comp, lift_fst, lift_snd, pF_id, pF_unit, zero_add]
  have hinj := GlobalTheory.Obs.Axes.injective_of_section N P hNP (fun p ↦ by
    rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2])
  refine hinj (?_ : N y = N 0)
  rw [map_zero]
  exact Prod.ext h₁ h₂

end GlobalTheory.AbCoh.AxesForm
