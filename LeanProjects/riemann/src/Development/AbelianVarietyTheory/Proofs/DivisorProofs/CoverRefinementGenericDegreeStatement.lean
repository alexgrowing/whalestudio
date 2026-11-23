import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_refinement_generic_degree : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (V' : Cover Y) (b : V'.X ⟶ V.X) (hb : b ≫ V.p = V'.p) (g : V'.G ⟶ V.G), V'.j ≫ b = g ≫ V.j → g ≫ V.π = V'.π → g (genericPoint V'.G) = genericPoint V.G → b (genericPoint V'.X) = genericPoint V.X ∧ b.residueDegree (genericPoint V'.X) * V.deg = V'.deg := by
  first | exact @GlobalTheory.CoverDeg.map_genericPoint_and_deg | exact GlobalTheory.CoverDeg.map_genericPoint_and_deg | (intros; apply GlobalTheory.CoverDeg.map_genericPoint_and_deg <;> assumption)
