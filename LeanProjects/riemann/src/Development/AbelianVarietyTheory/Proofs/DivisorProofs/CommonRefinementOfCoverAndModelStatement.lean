import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.common_refinement_of_cover_and_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (M : TrueGeo.Model Y), ∃ (V' : Cover Y) (a : V'.X ⟶ V.X) (g : V'.G ⟶ V.G) (b : V'.X ⟶ M.X), a ≫ V.p = V'.p ∧ b ≫ M.p = V'.p ∧ V'.j ≫ a = g ≫ V.j ∧ g ≫ V.π = V'.π ∧ g (genericPoint V'.G) = genericPoint V.G ∧ V'.j ≫ b = V'.π ≫ M.j := by
  first | exact @GlobalTheory.Mean4O.CoverDom.exists_cover_dominating | exact GlobalTheory.Mean4O.CoverDom.exists_cover_dominating | (intros; apply GlobalTheory.Mean4O.CoverDom.exists_cover_dominating <;> assumption)
