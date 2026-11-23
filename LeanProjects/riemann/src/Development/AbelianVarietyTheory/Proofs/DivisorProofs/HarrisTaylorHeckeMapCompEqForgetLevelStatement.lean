import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHeckeMapCompEqForgetLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_heckeMap_comp_eq_forgetLevel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (F : RepFam b N) (F₁ : RepFam b (N * k)) (F₂ : RepFam b (N * k * k)) (π : F₁.X ⟶ F.X) (π₁ : F₂.X ⟶ F₁.X), IsHeckeMap g c k N F F₁ π → IsHeckeMap g' c' k (N * k) F₁ F₂ π₁ → Nonempty (ObjMap (F₂.univ.forget N ⟨k * k, by ring⟩ hc) F.univ (π₁ ≫ π)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.heckeMap_comp_forget) | (exact GlobalTheory.UPel.HT.Hecke.heckeMap_comp_forget) | (intros; apply GlobalTheory.UPel.HT.Hecke.heckeMap_comp_forget <;> assumption)
