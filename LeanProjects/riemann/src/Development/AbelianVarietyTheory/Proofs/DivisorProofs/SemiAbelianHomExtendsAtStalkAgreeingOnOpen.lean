import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemiAbelianHomExtensionUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.StalkExt

theorem exists_agree_of_generic {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G]
    [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H)
    (hf : IsMonHom f) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (t : Sp R ⟶ S) [Mono t] (k : Sp (FractionRing R) ⟶ U) (hk : k ≫ j = Out.jK R ≫ t) :
    ∃ g : pullback G.hom t ⟶ H.left, g ≫ H.hom = pullback.fst G.hom t ≫ G.hom ∧
      GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom t) g := by
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing R (FractionRing R)

  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G (Out.jK R ≫ t))
    (((isGrpPullback_pullback ((Over.pullback j).obj G) k).comp (isGrpPullback_pullback G j)).congr hk rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback H (Out.jK R ≫ t))
    (((isGrpPullback_pullback ((Over.pullback j).obj H) k).comp (isGrpPullback_pullback H j)).congr hk rfl)
  haveI := ha; haveI := hb; haveI := hf
  have hfK : IsMonHom (a.hom ≫ (Over.pullback k).map f ≫ b.inv) := inferInstance
  have hρ : (a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k) ≫ pullback.fst G.hom j =
      pullback.fst G.hom (Out.jK R ≫ t) := (Category.assoc _ _ _).trans ha'
  have hb2 : b.inv.left ≫ pullback.fst H.hom (Out.jK R ≫ t) =
      pullback.fst ((Over.pullback j).obj H).hom k ≫ pullback.fst H.hom j := by
    rw [← hb', ← Category.assoc, ← Over.comp_left, b.inv_hom_id, Over.id_left, Category.id_comp]
  have hK : (a.hom ≫ (Over.pullback k).map f ≫ b.inv).left ≫ pullback.fst H.hom (Out.jK R ≫ t) =
      (a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k) ≫ f.left ≫ pullback.fst H.hom j := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb2, ← Category.assoc (((Over.pullback k).map f).left),
      GlobalTheory.ExtUnique.pullback_map_left_fst, Category.assoc, Category.assoc]

  obtain ⟨g, hg, hA⟩ := GlobalTheory.DedekindExt.exists_agree_of_extend (k := Out.jK R) (t := t) rfl G H
    (a.hom ≫ (Over.pullback k).map f ≫ b.inv) fun f' hf' => by
      obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.T.semiAbelian_hom_extends_from_generic_fibre R ((Over.pullback t).obj G) ((Over.pullback t).obj H)
        (IsSemiAbelian.pullback t G hG) (IsSemiAbelian.pullback t H hH) f' hf'
      exact ⟨F, hF⟩

  have hw : f.left ≫ pullback.snd H.hom j = pullback.snd G.hom j := Over.w f
  have hf₀ : (f.left ≫ pullback.fst H.hom j) ≫ H.hom = pullback.fst G.hom j ≫ G.hom := by
    refine (Category.assoc _ _ _).trans ?_
    rw [pullback.condition, pullback.condition, ← hw]
    exact (Category.assoc _ _ _).symm
  let c : pullback G.hom (Out.jK R ≫ t) ⟶ pullback G.hom t :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Out.jK R) (by rw [pullback.condition, Category.assoc])
  have hc₁ : c ≫ pullback.fst G.hom t = pullback.fst G.hom (Out.jK R ≫ t) := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd G.hom t = pullback.snd G.hom (Out.jK R ≫ t) ≫ Out.jK R := pullback.lift_snd _ _ _
  have sq : IsPullback c (pullback.snd G.hom (Out.jK R ≫ t)) (pullback.snd G.hom t) (Out.jK R) := by
    refine IsPullback.of_right ?_ hc₂ (IsPullback.of_hasPullback G.hom t)
    rw [hc₁]
    exact IsPullback.of_hasPullback G.hom (Out.jK R ≫ t)
  have : QuasiCompact c := MorphismProperty.of_isPullback sq.flip ‹_›
  have : IsSchemeTheoreticallyDominant c := .of_isPullback sq.flip
  refine ⟨g, hg, GlobalTheory.DedekindExt.Agree.of_dominant G.hom H.hom hf₀ hg c fun T u u' e => ?_⟩
  have h₁ := hA T (u ≫ c) u (by rw [Category.assoc, hc₁])
  have hu : u' = u ≫ a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k := by
    rw [← cancel_mono (pullback.fst G.hom j), ← e, Category.assoc, Category.assoc, hc₁, ← hρ, Category.assoc]
  rw [hu, ← Category.assoc, h₁, hK, Category.assoc, Category.assoc, Category.assoc]

theorem exists_agree_at_stalk : ∀ {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f → ∀ (s : S) [IsDomain (S.presheaf.stalk s)] [IsNoetherianRing (S.presheaf.stalk s)] [IsIntegrallyClosed (S.presheaf.stalk s)] (k : Sp (FractionRing (S.presheaf.stalk s)) ⟶ U), k ≫ j = ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s → ∃ g : pullback G.hom (S.fromSpecStalk s) ⟶ H.left, g ≫ H.hom = pullback.fst G.hom (S.fromSpecStalk s) ≫ G.hom ∧ GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom (S.fromSpecStalk s)) g := by
  intro U S j _ G H _ _ hG hH f hf s i₁ i₂ i₃ k hk
  haveI := i₁; haveI := i₂; haveI := i₃
  exact @exists_agree_of_generic U S j _ G H _ _ hG hH f hf (S.presheaf.stalk s) _ i₁ i₂ i₃ (S.fromSpecStalk s) _ k hk

end GlobalTheory.StalkExt
