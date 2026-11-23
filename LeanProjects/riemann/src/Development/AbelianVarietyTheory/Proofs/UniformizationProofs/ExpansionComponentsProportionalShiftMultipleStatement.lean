import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionComponentsProportionalShiftMultiple
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
theorem _root_.GlobalTheory.T.expansionComponents_proportional_shift_multiple : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → ∀ (α mu : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (Kbar V) N α mu) (DegPre.deltaε N))), u.IsGen → U.Supp (Kbar V) N α → ∃ a : Kbar V, ∀ t s, U.ExpF (Kbar V) N t s → ∀ z J, Good D.P.L z J → sval (s (α + N • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) a ⊤) * (sval (s α) (DegPre.trF D (Kbar V) mu).left z J * (val u (𝟙 _) z J).val)) := by
  first | exact @GlobalTheory.UU.SchurComp.components_proportional | exact GlobalTheory.UU.SchurComp.components_proportional | (intros; apply GlobalTheory.UU.SchurComp.components_proportional <;> assumption)
