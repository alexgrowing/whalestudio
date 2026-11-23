import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedMetricOfIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_metric_of_isometric : ∀ {F : Type} [Field F] [NumberField F] {C : TrueGeo.CxSt F} {Yv : ProjVar.Var F}
    (V : Cover Yv) (A : TrueGeo.Adl C Yv) (L M : HermLB V.p) (k : ℕ),
    V.Induces A L k → L.Isometric M → V.Induces A M k := by
  first | exact @GlobalTheory.InducesIsom.main | exact GlobalTheory.InducesIsom.main | (intros; apply GlobalTheory.InducesIsom.main <;> assumption)
