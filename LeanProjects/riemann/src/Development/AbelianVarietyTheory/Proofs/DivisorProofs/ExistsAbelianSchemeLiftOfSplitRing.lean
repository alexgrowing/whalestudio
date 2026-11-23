import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitSpecQuotientComplementaryIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSpMapQuotientSpanBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoprodDescOfSmoothPiecesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackCoprodDescOfPiecesOverCoprodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawGlueOverCoprodBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeSmoothLiftNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickeningStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLiftGlue

theorem exists_lift_of_split : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (e : R), IsIdempotentElem e → ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ → (∀ f : R, (f = e ∨ f = 1 - e) → ∃ (A : Over (Sp (R ⧸ Ideal.span {f}))) (_ : GrpObj A) (B : Over (Sp (R₀ ⧸ Ideal.span {π f}))) (_ : GrpObj B) (i : B.left ⟶ A.left) (j : B.left ⟶ A₀.left) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π ∧ IsGrpPullback B A (spMap ρ) i ∧ IsGrpPullback B A₀ (spMap (Ideal.Quotient.mk _)) j ∧ IsAbelianScheme A) → ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A := by
  intro R R₀ _ _ I hI π hπ hk e he A₀ _ hA₀ H
  obtain ⟨A₁, gA₁, B₁, gB₁, i₁, j₁, ρ₁, hρ₁, hp₁, hq₁, hab₁⟩ := H e (Or.inl rfl)
  obtain ⟨A₂, gA₂, B₂, gB₂, i₂, j₂, ρ₂, hρ₂, hp₂, hq₂, hab₂⟩ := H (1 - e) (Or.inr rfl)
  have cS := GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents R e (1 - e) he (by ring)
  have cT := GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents R₀ (π e) (π (1 - e)) (he.map π) (by rw [← map_add]; simp)
  obtain ⟨i, hi₁, hi₂, hpb⟩ := GlobalTheory.T.isPullback_coprodDesc_of_pieces_over_coprod _ _ cS _ _ cT (spMap π) (spMap ρ₁) (spMap ρ₂) (GlobalTheory.T.isPullback_spMap_quotient_span_baseChange R R₀ π e ρ₁ hρ₁) (GlobalTheory.T.isPullback_spMap_quotient_span_baseChange R R₀ π (1 - e) ρ₂ hρ₂)
    A₁.hom A₂.hom A₀.hom B₁.hom B₂.hom j₁ j₂ i₁ i₂ hq₁.1 hq₂.1 hp₁.1 hp₂.1
  have hsm := GlobalTheory.T.smooth_coprodDesc_of_smooth_pieces _ _ cS A₁.hom A₂.hom hab₁.smooth hab₂.smooth
  set X : Over (Sp R) := Over.mk (Limits.coprod.desc (A₁.hom ≫ spMap (Ideal.Quotient.mk (Ideal.span {e}))) (A₂.hom ≫ spMap (Ideal.Quotient.mk (Ideal.span {1 - e})))) with hX
  obtain ⟨m, hm⟩ := GlobalTheory.T.groupLaw_glue_over_coprod_base _ _ cS _ _ cT (spMap ρ₁) (spMap ρ₂) A₁ A₂ B₁ B₂ A₀ i₁ i₂ j₁ j₂ hp₁ hp₂ hq₁ hq₂ i hi₁ hi₂
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk, hI]⟩
  have hsm' : Smooth X.hom := hsm
  have hpb' : IsPullback i A₀.hom X.hom (spMap π) := hpb
  obtain ⟨e₁, he₁, he₁'⟩ := GlobalTheory.T.exists_section_lift_smooth_nilpotent_thickening R R₀ π hπ hnil X A₀ i hpb' hsm' (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left (Over.w _)
  have hw : ∀ g : A₀ ⊗ A₀ ⟶ A₀, (g.left ≫ i) ≫ X.hom = (Over.mk ((A₀ ⊗ A₀).hom ≫ spMap π)).hom := fun g ↦ by
    simp only [Over.mk_hom, Category.assoc, hpb'.w]; rw [← Category.assoc, Over.w]
  let l : Over.mk ((A₀ ⊗ A₀).hom ≫ spMap π) ⟶ X ⊗ X := lift (Over.homMk _ (hw (fst A₀ A₀))) (Over.homMk _ (hw (snd A₀ A₀)))
  have hl₁ : l.left ≫ (fst X X).left = (fst A₀ A₀).left ≫ i := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hl₂ : l.left ≫ (snd X X).left = (snd A₀ A₀).left ≫ i := by
    rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨g, hg, hab⟩ := GlobalTheory.T.exists_grpObj_isAbelianScheme_smoothLift_nilpotent R R₀ π hπ hnil A₀ hA₀ X i hpb' hsm' e₁ he₁ he₁' l.left hl₁ hl₂ m (hm l.left hl₁ hl₂)
  exact ⟨X, g, i, hg, hab⟩

end GlobalTheory.AbLiftGlue
