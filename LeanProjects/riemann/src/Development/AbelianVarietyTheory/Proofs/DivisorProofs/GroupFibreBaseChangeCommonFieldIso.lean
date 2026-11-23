import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.FibBC

theorem pullCompIso_hom_eq {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).hom = (Over.pullbackComp p f).hom.app G := Category.comp_id _

theorem pullCompIso_fst {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).hom.left ≫ pullback.fst _ p ≫ pullback.fst G.hom f = pullback.fst G.hom (p ≫ f) := by
  rw [pullCompIso_hom_eq]
  simp [Over.pullbackComp, Over.mapComp, pullback.lift_fst_assoc, pullback.lift_fst]

theorem pullCompIso_inv_fst {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).inv.left ≫ pullback.fst G.hom (p ≫ f) = pullback.fst _ p ≫ pullback.fst G.hom f := by
  rw [← pullCompIso_fst, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]

theorem pullback_map_fst {S S' : Scheme.{0}} (g : S' ⟶ S) {A B : Over S} (u : A ⟶ B) :
    ((Over.pullback g).map u).left ≫ pullback.fst B.hom g = pullback.fst A.hom g ≫ u.left :=
  pullback.lift_fst _ _ _

theorem fibre_baseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W'] (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left), IsGrpPullback G' G ξ' β → ∀ (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W') (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y), IsMonHom e'.hom → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (i₂ : ResidueField W' →+* Ω'), spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ' → io.comp κ = i₂.comp κ' → ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y) (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left), IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧ e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') := by
  intro S G _ W' _ _ G' _ ξ' β hβ k _ Y _ κ' e' he' Ω _ x κ Ω' _ io i₂ hc hκ
  have hm : spMap i₂ ≫ spMap κ' = spMap (io.comp κ) := by
    rw [hκ, ← Spec.map_comp]; rfl
  rw [← hm]

  have h₁ : IsGrpPullback ((Over.pullback (spMap i₂ ≫ spMap (residue W'))).obj G') G (spMap io ≫ x)
      (pullback.fst G'.hom (spMap i₂ ≫ spMap (residue W')) ≫ β) :=
    ((isGrpPullback_pullback G' (spMap i₂ ≫ spMap (residue W'))).comp hβ).congr
      (by rw [hc, Category.assoc]) rfl
  obtain ⟨e₁, he₁, he₁f⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap io ≫ x)) h₁
  let e₂ := pullCompIso (spMap i₂) (spMap (residue W')) G'
  let e₃ := (Over.pullback (spMap i₂)).mapIso e'
  let e₄ := (pullCompIso (spMap i₂) (spMap κ') Y).symm
  have i₃ : IsMonHom e₃.hom := by show IsMonHom ((Over.pullback (spMap i₂)).map e'.hom); infer_instance
  have i₄ : IsMonHom e₄.hom := by show IsMonHom (pullCompIso (spMap i₂) (spMap κ') Y).inv; infer_instance
  have f₂ : e₂.hom.left ≫ pullback.fst _ (spMap i₂) ≫ pullback.fst G'.hom (spMap (residue W')) =
      pullback.fst G'.hom (spMap i₂ ≫ spMap (residue W')) := pullCompIso_fst _ _ _
  have f₃ : e₃.hom.left ≫ pullback.fst _ (spMap i₂) = pullback.fst _ (spMap i₂) ≫ e'.hom.left :=
    pullback_map_fst _ _
  have f₄ : e₄.hom.left ≫ pullback.fst Y.hom (spMap i₂ ≫ spMap κ') =
      pullback.fst _ (spMap i₂) ≫ pullback.fst Y.hom (spMap κ') := pullCompIso_inv_fst _ _ _
  refine ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄, e₁.hom.left ≫ e₂.hom.left ≫ pullback.fst _ (spMap i₂), ?_, ?_, ?_⟩
  · show IsMonHom (e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom); infer_instance
  · rw [Category.assoc, Category.assoc, reassoc_of% f₂, he₁f]
  · show (e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom).left ≫ _ = _
    simp only [Over.comp_left, Category.assoc]
    rw [f₄, reassoc_of% f₃]

end GlobalTheory.Mum.FibBC
