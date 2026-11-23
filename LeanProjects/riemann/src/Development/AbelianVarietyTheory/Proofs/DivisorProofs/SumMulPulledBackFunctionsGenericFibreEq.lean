import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_app_eq_sum_mul_of_comm : ∀ {X Y S S' T X' : Scheme.{0}} (g : X ⟶ S) (h : S' ⟶ S) (gp : T ⟶ S) (gp' : T ⟶ S') (hgp : gp' ≫ h = gp) (fst : X' ⟶ X) (snd : X' ⟶ S'), fst ≫ g = snd ≫ h → ∀ (α : Y ⟶ X) (t : Y ⟶ T) (hpb : α ≫ g = t ≫ gp) (l : Y ⟶ X') (h1 : l ≫ fst = α), l ≫ snd = t ≫ gp' → ∀ (W : X.Opens) (U : S.Opens) (hWU : W ≤ g ⁻¹ᵁ U) (n : ℕ) (c : Fin n → Γ(X, W)) (b : Fin n → Γ(T, gp ⁻¹ᵁ U)) (b' : Fin n → Γ(S', h ⁻¹ᵁ U)), (∀ m, (gp'.appLE (h ⁻¹ᵁ U) (gp ⁻¹ᵁ U) (le_preimage_of_comp_eq gp gp' h hgp U)).hom (b' m) = b m) → ∃ y : Γ(X', fst ⁻¹ᵁ W), (l.app (fst ⁻¹ᵁ W)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_le l fst α h1 W)).op).hom (∑ m, (α.app W).hom (c m) * (t.appLE (gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen g α t gp hpb W U hWU)).hom (b m)) := by
  intro X Y S S' T X' g h gp gp' hgp fst snd hsq α t hpb l h1 h2 W U hWU n c b b' hb
  subst h1
  have le : fst ⁻¹ᵁ W ≤ snd ⁻¹ᵁ (h ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← hsq, Scheme.Hom.comp_preimage]
    exact fun x hx => hWU hx
  refine ⟨∑ m, (fst.app W).hom (c m) * (snd.appLE (h ⁻¹ᵁ U) (fst ⁻¹ᵁ W) le).hom (b' m), ?_⟩
  have hid : ∀ z : Γ(Y, (l ≫ fst) ⁻¹ᵁ W), (Y.presheaf.map (homOfLE (extLI_preimage_le l fst (l ≫ fst) rfl W)).op).hom z = z := by
    intro z
    have : (homOfLE (extLI_preimage_le l fst (l ≫ fst) rfl W)).op = 𝟙 (Opposite.op ((l ≫ fst) ⁻¹ᵁ W)) := rfl
    erw [this, Y.presheaf.map_id]
    rfl
  rw [hid, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  rw [← hb m]
  have key : ∀ (f₁ f₂ : Y ⟶ S') (e : f₁ = f₂) (V : Y.Opens) (e₁ e₂), f₁.appLE (h ⁻¹ᵁ U) V e₁ = f₂.appLE (h ⁻¹ᵁ U) V e₂ := by
    intro f₁ f₂ e V e₁ e₂; subst e; rfl
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (b' m)) (key _ _ h2 _ _ _)

end GlobalTheory.Mum
