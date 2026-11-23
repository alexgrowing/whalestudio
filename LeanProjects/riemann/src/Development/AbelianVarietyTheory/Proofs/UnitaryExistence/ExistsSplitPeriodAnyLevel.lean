import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfDefinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPureTypePeriodOfSignatureSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_isSplit_period_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ i, ∃ (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), IsSplit hP := by
  intro E _ _ _ H D l Xo σ g ty F _ _ hty hc i
  have hp : (F.Di i).p = D.p := (F.sig i).1
  have hq : (F.Di i).q = D.q := (F.sig i).2
  refine exists_isSplit_of_splitLat E H (F.Di i) g ty (by rw [hp, hq]; exact hty) ?_
  by_cases h0 : D.p = 0 ∨ D.q = 0
  · exact splitLat_of_definite E H (F.Di i) (by rw [hp, hq]; exact h0)
  · have h1 : D.p ≠ 0 := fun h => h0 (Or.inl h)
    have h2 : D.q ≠ 0 := fun h => h0 (Or.inr h)
    rcases hc with h | h | ⟨h3, h4⟩
    · exact absurd h h1
    · exact absurd h h2
    · exact GlobalTheory.SplitGenus.splitLat_of_indefinite E H (F.Di i) h4 (by omega) (by omega) (by omega)

end GlobalTheory.CompRat
