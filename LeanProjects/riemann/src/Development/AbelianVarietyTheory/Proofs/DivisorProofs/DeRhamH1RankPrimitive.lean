import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToStructureH1SurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfFormInjectiveOfH0Const
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgProjectiveConstantRankExtensionAndProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfSplitInjectiveFgProjectiveConstantRanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsProjectiveRankStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem fp_HH1 (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) : FP R (HH1 A.hom) (2 * g) := by
  have hcl := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hA hs
  have h0 := (GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs).2.1
  have hinj : Function.Injective (clAll (OAff A.hom) hcl) := by
    unfold clAll
    exact (ofForm_injective_of_H0Const R _ _ h0).comp (LinearEquiv.ofTop _ hcl).symm.injective
  have hex : Function.Exact (clAll (OAff A.hom) hcl) (toHO1 A.hom) := by
    rw [LinearMap.exact_iff]
    change Fil1 (OAff A.hom) = _
    rw [Fil1_eq_range]
    unfold clAll
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  have := (GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod).1 R _ _ _ g g _ _ hinj (GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hA hs) hex
    (GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hs) (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs).1
  rwa [two_mul]

theorem rank_prim_HH1 : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → FP R (HH1 A.hom) (2 * g) ∧ DeRhamH1Primitive A := by
  intro R _ A _ g hA hs
  refine ⟨fp_HH1 R A g hA hs, fun x ↦ ?_⟩
  obtain ⟨-, -, hAA, hsAA⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  have ax := (GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A).2.2
  set i₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  set i₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  let f : HH1 A.hom × HH1 A.hom →ₗ[R] HH1 (A ⊗ A).hom :=
    (deRhamH1Pullback (fst A A)).coprod (deRhamH1Pullback (snd A A))
  let r : HH1 (A ⊗ A).hom →ₗ[R] HH1 A.hom × HH1 A.hom := (deRhamH1Pullback i₁).prod (deRhamH1Pullback i₂)
  have hrf : ∀ p, r (f p) = p := by
    rintro ⟨a, b⟩
    show (deRhamH1Pullback i₁ (deRhamH1Pullback (fst A A) a + deRhamH1Pullback (snd A A) b), deRhamH1Pullback i₂ (deRhamH1Pullback (fst A A) a + deRhamH1Pullback (snd A A) b)) = (a, b)
    rw [map_add, map_add, (ax a).1, (ax b).2.1, (ax a).2.2.2.1, (ax b).2.2.2.2.1, add_zero, zero_add]
  have hM : FP R (HH1 A.hom × HH1 A.hom) (2 * (g + g)) := by
    have := (GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod).2 R _ _ _ _ (fp_HH1 R A g hA hs) (fp_HH1 R A g hA hs)
    rwa [← mul_add] at this
  have hbij := GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank R _ _ _ hM (fp_HH1 R (A ⊗ A) (g + g) hAA hsAA) f r hrf
  obtain ⟨p, hp⟩ := hbij.2 (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x)
  have hry : r (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x) = 0 := by
    show (deRhamH1Pullback i₁ (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x),
      deRhamH1Pullback i₂ (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x)) = (0, 0)
    rw [map_sub, map_sub, map_sub, map_sub, (ax x).1, (ax x).2.1, (ax x).2.2.1,
      (ax x).2.2.2.1, (ax x).2.2.2.2.1, (ax x).2.2.2.2.2, sub_self, sub_zero, sub_zero, sub_self]
  have hp0 : p = 0 := by rw [← hrf p, hp, hry]
  have h0 : deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x = 0 := by rw [← hp, hp0, map_zero]
  rw [sub_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.AbCoh
