import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFreeModuleIso
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_free_module_iso : ∀ (S T : Scheme.{0}) (f : S ⟶ T) (n : ℕ), Nonempty ((Scheme.Modules.pullback f).obj (GlobalTheory.QCoh.freeModule (X := T) (Fin n)) ≅ GlobalTheory.QCoh.freeModule (X := S) (Fin n)) := by
  first | exact @GlobalTheory.pullback_freeModule_iso_free | exact GlobalTheory.pullback_freeModule_iso_free | (intros; apply GlobalTheory.pullback_freeModule_iso_free <;> assumption)
