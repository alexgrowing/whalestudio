import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemiAbelianHomExtensionUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsAtStalkAgreeingOnOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGenericPointStalkSubsetOfDenseOpenStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SemiAbDenseExt

theorem exists_extension : ∀ {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S] [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j], Dense (Set.range j) → ∀ (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ (A B : Over U) [GrpObj A] [GrpObj B] (φ : A.left ⟶ G.left) (ψ : B.left ⟶ H.left), IsGrpPullback A G j φ → IsGrpPullback B H j ψ → ∀ g : A ⟶ B, IsMonHom g → ∃ f : G ⟶ H, g.left ≫ ψ = φ ≫ f.left := by
  intro U S _ _ j _ hd G H _ _ hG hH A B _ _ φ ψ hA hB g hg
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G j) hA
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hB (isGrpPullback_pullback H j)
  let f := a.hom ≫ g ≫ b.hom
  have hf : IsMonHom f := by infer_instance
  have : IsDominant j := ⟨hd⟩
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.dense_openImmersion j
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  have := hG.smooth
  have := hH.smooth
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have hw : f.left ≫ pullback.snd H.hom j = pullback.snd G.hom j := Over.w f
  have hf₀ : (f.left ≫ pullback.fst H.hom j) ≫ H.hom = pullback.fst G.hom j ≫ G.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw, pullback.condition]
  obtain ⟨F, hF, hF'⟩ := GlobalTheory.DedekindExt.exists_of_stalks (j := j) G.hom H.hom
    (IsPullback.of_hasPullback G.hom j) hf₀ fun s => by
      obtain ⟨k, hk⟩ : ∃ k : Sp (FractionRing (S.presheaf.stalk s)) ⟶ U,
          k ≫ j = ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s :=
        ⟨IsOpenImmersion.lift j _ (GlobalTheory.T.range_genericPoint_stalk_subset_of_denseOpen j hd s), IsOpenImmersion.lift_fac _ _ _⟩
      obtain ⟨g', hg', hA'⟩ := GlobalTheory.T.semiAbelian_hom_extends_at_stalk_agreeing_on_open j G H hG hH f hf s k hk
      exact ⟨_, S.fromSpecStalk s, 𝟙 _, g', Category.id_comp _, hg', hA'⟩
  refine ⟨Over.homMk F hF, ?_⟩
  have hφ : φ = a.inv.left ≫ pullback.fst G.hom j := by
    rw [← ha', ← Category.assoc, ← Over.comp_left, a.inv_hom_id, Over.id_left, Category.id_comp]
  show g.left ≫ ψ = φ ≫ F
  rw [hφ, Category.assoc, hF']
  simp only [f, Over.comp_left, Category.assoc, hb']
  rw [← Category.assoc a.inv.left, ← Over.comp_left, a.inv_hom_id, Over.id_left, Category.id_comp]

end GlobalTheory.SemiAbDenseExt
