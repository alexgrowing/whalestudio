import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgProjectiveConstantRankExtensionAndProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfSplitInjectiveFgProjectiveConstantRanStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem axesO1_of_isAbelianScheme (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) : AxesVanishingStructureSheafDegOne A := by
  obtain ⟨-, -, hAA, hgg⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  have h1 := (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hg).1
  have h2 := (GlobalTheory.T.abelian_structure_cohomology_statement R (A ⊗ A) (g + g) hAA hgg).1
  have hax := (GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A).1
  let f : HO1 A.hom × HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom :=
    pO1 (fst A A) ∘ₗ LinearMap.fst R _ _ + pO1 (snd A A) ∘ₗ LinearMap.snd R _ _
  let r : HO1 (A ⊗ A).hom →ₗ[R] HO1 A.hom × HO1 A.hom :=
    LinearMap.prod (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))) (pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)))
  have hrf : ∀ x, r (f x) = x := by
    rintro ⟨a, b⟩
    have e : f (a, b) = pO1 (fst A A) a + pO1 (snd A A) b := rfl
    have e2 : ∀ z, r z = (pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) z, pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) z) :=
      fun _ ↦ rfl
    rw [e2, e, map_add, map_add, (hax a).1, (hax b).2.1, (hax a).2.2.2.1, (hax b).2.2.2.2.1, add_zero, zero_add]
  have hP := (GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod).2 R _ _ g g h1 h1
  have hbij := GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank R _ _ (g + g) hP h2 f r hrf
  intro y hy1 hy2
  obtain ⟨x, rfl⟩ := hbij.2 y
  have h0 : r (f x) = 0 := Prod.ext hy1 hy2
  rw [hrf] at h0
  rw [h0, map_zero]

theorem primO1_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A := by
  intro R _ A _ g hA hg x
  have hax := (GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A).1 x
  have h := axesO1_of_isAbelianScheme R A g hA hg (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x)
    (by rw [map_sub, map_sub, hax.1, hax.2.1, hax.2.2.1, sub_self, sub_zero])
    (by rw [map_sub, map_sub, hax.2.2.2.1, hax.2.2.2.2.1, hax.2.2.2.2.2, sub_zero, sub_self])
  rw [sub_sub, sub_eq_zero] at h
  exact h

end GlobalTheory.AbCoh
