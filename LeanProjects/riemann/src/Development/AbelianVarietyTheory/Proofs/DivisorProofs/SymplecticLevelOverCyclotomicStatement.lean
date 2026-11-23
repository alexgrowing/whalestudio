import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelOverCyclotomic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_level_over_cyclotomic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N M e : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e →
  (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P (Module.finrank ℤ D.La / 2) M (zetaAway M) s₁ lev →
    HarrisTaylorSymplecticLevelFamilyUniversalProperty b N (Module.finrank ℤ D.La / 2) M s s₁ u lev →
    ∀ ρ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X)
        (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover (sympSimGrp (Module.finrank ℤ D.La / 2) M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
        y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  first | (exact @GlobalTheory.HTSympCover.exists_galoisCover) | (exact GlobalTheory.HTSympCover.exists_galoisCover) | (intros; apply GlobalTheory.HTSympCover.exists_galoisCover <;> assumption)
