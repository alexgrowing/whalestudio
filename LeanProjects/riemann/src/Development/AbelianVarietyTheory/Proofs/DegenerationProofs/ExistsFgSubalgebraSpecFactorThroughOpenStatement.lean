import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFgSubalgebraSpecFactorThroughOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fg_subalgebra_spec_factor_through_open : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω), R.FG → ∀ V : (Sp R).Opens, (V : Set (Sp R)).Nonempty → ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧ ∃ τ : Sp R' ⟶ V.toScheme, τ ≫ V.ι = spMap (Subalgebra.inclusion h).toRingHom := by
  first | exact @GlobalTheory.exists_fg_subalgebra_spec_factors_open | exact GlobalTheory.exists_fg_subalgebra_spec_factors_open | (intros; apply GlobalTheory.exists_fg_subalgebra_spec_factors_open <;> assumption)
