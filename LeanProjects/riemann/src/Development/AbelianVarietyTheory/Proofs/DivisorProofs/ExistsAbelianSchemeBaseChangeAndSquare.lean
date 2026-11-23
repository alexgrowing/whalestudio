import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
open CategoryTheory Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbBaseChangeSq

theorem exists_baseChange_and_sq : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (A : Over (Sp R₀)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (B : Over (Sp R₁)) (_ : GrpObj B) (pr : B.left ⟶ A.left) (pr' : (B ⊗ B).left ⟶ (A ⊗ A).left), IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsPullback pr B.hom A.hom (spMap (algebraMap R₀ R₁)) ∧ IsPullback pr' (B ⊗ B).hom (A ⊗ A).hom (spMap (algebraMap R₀ R₁)) ∧ (μ[B]).left ≫ pr = pr' ≫ (μ[A]).left ∧ (fst B B).left ≫ pr = pr' ≫ (fst A A).left ∧ (snd B B).left ≫ pr = pr' ≫ (snd A A).left ∧ (CartesianMonoidalCategory.lift (𝟙 B) (1 : B ⟶ B)).left ≫ pr' = pr ≫ (CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ A)).left ∧ (CartesianMonoidalCategory.lift (1 : B ⟶ B) (𝟙 B)).left ≫ pr' = pr ≫ (CartesianMonoidalCategory.lift (1 : A ⟶ A) (𝟙 A)).left := by
  intro R₀ R₁ _ _ _ A _ g hA hg
  let f : Sp R₁ ⟶ Sp R₀ := spMap (algebraMap R₀ R₁)
  let F := Over.pullback f
  let B : Over (Sp R₁) := F.obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsGrpPullback B A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨hAB, hgB⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ A B _ g hB hA hg
  have mapL : ∀ {X Y : Over (Sp R₀)} (a : X ⟶ Y),
      (F.map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left := fun a => pullback.lift_fst _ _ _
  let m := Functor.LaxMonoidal.μ F A A
  refine ⟨B, inferInstance, pullback.fst A.hom f, m.left ≫ pullback.fst (A ⊗ A).hom f, hAB, hgB, hB.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : IsIso m := inferInstanceAs (IsIso (Functor.Monoidal.μIso F A A).hom)
    haveI : IsIso m.left := (Over.forget _).map_isIso m
    have h1 : IsPullback m.left (B ⊗ B).hom (F.obj (A ⊗ A)).hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w m⟩
    have h2 := h1.paste_horiz (IsPullback.of_hasPullback (A ⊗ A).hom f)
    rwa [Category.id_comp] at h2
  · have e : μ[B] = m ≫ F.map μ[A] := Functor.obj.μ_def (F := F) A
    rw [e, Over.comp_left, Category.assoc, mapL, Category.assoc]
  · rw [Category.assoc, ← mapL, ← Category.assoc, ← Over.comp_left]
    simp [m]
    rfl
  · rw [Category.assoc, ← mapL, ← Category.assoc, ← Over.comp_left]
    simp [m]
    rfl
  · have e : lift (𝟙 B) (1 : B ⟶ B) ≫ m = F.map (lift (𝟙 A) (1 : A ⟶ A)) := by
      rw [← Functor.Monoidal.lift_μ, F.map_id, Functor.map_one]
    rw [← Category.assoc, ← Over.comp_left, e, mapL]
  · have e : lift (1 : B ⟶ B) (𝟙 B) ≫ m = F.map (lift (1 : A ⟶ A) (𝟙 A)) := by
      rw [← Functor.Monoidal.lift_μ, F.map_id, Functor.map_one]
    rw [← Category.assoc, ← Over.comp_left, e, mapL]

end GlobalTheory.AbBaseChangeSq
