import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.siegelObject_pullback_exists_and_principal : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (c : SiegPre h M ζ s), f ≫ s = s' → (∃ c' : SiegPre h M ζ s', SiegPB c' c f) ∧ ∀ c' : SiegPre h M ζ s', SiegPB c' c f → c.Principal → c'.Principal := by
  first | exact @GlobalTheory.siegPre_pullback | exact GlobalTheory.siegPre_pullback | (intros; apply GlobalTheory.siegPre_pullback <;> assumption)
