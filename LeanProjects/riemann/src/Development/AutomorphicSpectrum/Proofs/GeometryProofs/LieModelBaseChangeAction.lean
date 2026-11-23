import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ActBC

theorem exists_act_extends : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (O : Type) [CommRing O] (act : OAct O G) (act' : OAct O G'), (∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → Submodule.span L' (Set.range j) = ⊤ → ∀ ρ : O →+* Module.End L V, MV.IsActOf act.act ρ → ∃ ρ' : O →+* Module.End L' V', MV'.IsActOf act'.act ρ' ∧ ∀ a x, ρ' a (j x) = j (ρ a x) := by
  intro L L' _ _ e G G' _ _ φ hpb O _ act act' hcomm V V' _ _ _ _ MV MV' j hj hspan ρ hρ
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ _ _ _ _ MV' _ act'.act act'.hom act'.one
    act'.mul act'.add
  refine ⟨ρ', hρ', fun a x => ?_⟩
  apply MV'.inj
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · rw [hρ' a (j x), Over.comp_left, Category.assoc, hcomm a, ← Category.assoc, hj x, Category.assoc,
      ← Over.comp_left, ← hρ a x, hj (ρ a x)]
  · rw [Over.w, Over.w]

end GlobalTheory.CompanionTheory.Ar.ActBC
