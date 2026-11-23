import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ (α : D.X) t s, U.ExpF (Kbar V) N t s → ∃ t' s', U.ExpF (Kbar V) N t' s' ∧ ∀ β, (∃ mu, β = α + N • mu) ∧ s' β = s β ∨ (¬ ∃ mu, β = α + N • mu) ∧ ∀ j, (s' β).f j = 0) ∧ (∀ α : D.X, ∃ mu, U.Supp (Kbar V) N (α + N • mu)) ∧ ∀ (α : D.X), U.Supp (Kbar V) N α → ∀ t s, U.ExpF (Kbar V) N t s → (∀ β, (¬ ∃ mu, β = α + N • mu) → ∀ j, (s β).f j = 0) → (∀ j, (s α).f j = 0) → ∀ j, t.f j = 0) := by
  first | exact @GlobalTheory.UU.Weight.main | exact GlobalTheory.UU.Weight.main | (intros; apply GlobalTheory.UU.Weight.main <;> assumption)
