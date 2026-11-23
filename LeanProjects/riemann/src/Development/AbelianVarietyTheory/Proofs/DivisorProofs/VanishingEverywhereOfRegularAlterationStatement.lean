import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingEverywhereOfRegularAlteration
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSectionLiftsMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricSetupStatement
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TwoLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_everywhere_of_regular_alteration : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → VanishOn RegFlagged → VanishOn fun _ _ _ _ _ _ => True := by
  first | exact @GlobalTheory.TwoLat.Gen.vanishOn_of_regFlagged | exact GlobalTheory.TwoLat.Gen.vanishOn_of_regFlagged | (intros; apply GlobalTheory.TwoLat.Gen.vanishOn_of_regFlagged <;> assumption)
