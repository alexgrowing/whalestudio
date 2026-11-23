import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomAlgebraisingThickeningsProjectiveStatement
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MorAlgTower

theorem step_comm {C : Type*} [Category C] {Y Y' B S S' T : C} {p : B ⟶ T} {t : S ⟶ T}
    {t' : S' ⟶ T} [HasPullback p t] [HasPullback p t'] {τ : S ⟶ S'} {β : Y ⟶ Y'} {b : Y ⟶ B}
    {b' : Y' ⟶ B} {y : Y ⟶ S} {y' : Y' ⟶ S'} (hb : IsPullback b y p t)
    (hb' : IsPullback b' y' p t') (h₁ : β ≫ b' = b) (h₂ : β ≫ y' = y ≫ τ)
    (e₁ : p ≫ 𝟙 T = 𝟙 B ≫ p) (e₂ : t ≫ 𝟙 T = τ ≫ t') {Z : C} {c : Y ⟶ Z} {c' : Y' ⟶ Z}
    (hc : β ≫ c' = c) :
    pullback.map p t p t' (𝟙 _) τ (𝟙 _) e₁ e₂ ≫ hb'.isoPullback.inv ≫ c'
      = hb.isoPullback.inv ≫ c := by
  have key : β ≫ hb'.isoPullback.hom
      = hb.isoPullback.hom ≫ pullback.map p t p t' (𝟙 _) τ (𝟙 _) e₁ e₂ := by
    apply pullback.hom_ext
    · simp [h₁, pullback.map, pullback.lift_fst]
    · simp [h₂, pullback.map, pullback.lift_snd]
  rw [Iso.eq_inv_comp, ← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id_assoc, hc]

theorem base_comm {C : Type*} [Category C] {Y B S T Z : C} {p : B ⟶ T} {t : S ⟶ T}
    [HasPullback p t] {b : Y ⟶ B} {y : Y ⟶ S} (hb : IsPullback b y p t) {c : Y ⟶ Z} {z : Z ⟶ T}
    (hc : c ≫ z = y ≫ t) : (hb.isoPullback.inv ≫ c) ≫ z = pullback.fst p t ≫ p := by
  rw [← hb.isoPullback_inv_fst, Category.assoc, Category.assoc, hc, hb.w]

theorem final_comm {C : Type*} [Category C] {Y B S T Z : C} {p : B ⟶ T} {t : S ⟶ T}
    [HasPullback p t] {b : Y ⟶ B} {y : Y ⟶ S} (hb : IsPullback b y p t) {c : Y ⟶ Z} {g : B ⟶ Z}
    (hg : pullback.fst p t ≫ g = hb.isoPullback.inv ≫ c) : b ≫ g = c := by
  have h := hb.isoPullback_hom_fst
  calc b ≫ g = (hb.isoPullback.hom ≫ pullback.fst p t) ≫ g := by rw [h]
    _ = c := by rw [Category.assoc, hg, Iso.hom_inv_id_assoc]

theorem exists_hom_of_tower : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ Z : Over (Spec (CommRingCat.of R)), IsProjBy Z.hom → ∀ c : ∀ e, (Y e).left ⟶ Z.left, (∀ e, c e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ c (e + 1) = c e) → ∃ g : B ⟶ Z, ∀ e, b e ≫ g.left = c e := by
  intro R _ _ _ I hI hc Y β hβ B b hB hfl hb hβb Z hZ c hcZ hβc
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_hom_algebraising_thickenings_projective R I hI hc B Z hB hZ hfl (fun e => (hb e).isoPullback.inv ≫ c e)
    (fun e => base_comm (hb e) (hcZ e))
    (fun e => step_comm (hb e) (hb (e + 1)) (hβb e) (hβ e).w _ _ (hβc e))
  exact ⟨g, fun e => final_comm (hb e) (hg e)⟩

end GlobalTheory.MorAlgTower
