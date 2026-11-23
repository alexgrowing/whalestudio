import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem morphisms_eq_spread_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ Z : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (q : Z ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [LocallyOfFiniteType q] (a b : X₀ ⟶ Z), IsPullback π f f₀ (spMap R₀.subtype) → a ≫ q = f₀ → b ≫ q = f₀ → π ≫ a = π ≫ b → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hle)) → π₁ ≫ a = π₁ ≫ b := by
  intro S _ R₀ X X₀ Z f f₀ q π _ _ a b hp ha hb hab
  have hp' : IsPullback π f f₀ (spMap (algebraMap R₀ S)) := hp
  have hfst : pullback.fst f₀ (spMap (algebraMap R₀ S)) = hp'.isoPullback.inv ≫ π := by
    rw [hp'.isoPullback_inv_fst]
  obtain ⟨R', hR', ⟨s, rfl⟩, h⟩ := Spread.exists_fg_comp_eq_comp (A := S) f₀ q ⊥ Subalgebra.fg_bot
    (pullback.fst _ _ ≫ a) (pullback.fst _ _ ≫ b)
    (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb])
    (by rw [Spread.bcMap_fst_assoc, Spread.bcMap_fst_assoc, hfst, Category.assoc, Category.assoc, hab])
  rw [Spread.bcMap_fst_assoc, Spread.bcMap_fst_assoc] at h
  refine ⟨s, fun R₁ h₀ hs X₁ f₁ π₁ hp₁ ↦ ?_⟩
  have hle : (Algebra.adjoin R₀ (s : Set S)).toSubring ≤ R₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h₀ r.2
    | add x y _ _ hx hy => exact R₁.add_mem hx hy
    | mul x y _ _ hx hy => exact R₁.mul_mem hx hy
  let g : Algebra.adjoin R₀ (s : Set S) →+* R₁ := Subring.inclusion hle
  have hg : spMap g ≫ spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))) =
      spMap (Subring.inclusion h₀) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let m : X₁ ⟶ pullback f₀ (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S)))) :=
    pullback.lift π₁ (f₁ ≫ spMap g) (by rw [Category.assoc, hg, hp₁.w])
  have hm : m ≫ pullback.fst _ _ = π₁ := pullback.lift_fst _ _ _
  rw [← hm, Category.assoc, Category.assoc, h]

end GlobalTheory
