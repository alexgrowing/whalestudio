import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedModelDeRhamOfHeightAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamModelDR
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.CovTestDR GlobalTheory.EigWhole
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_model_de_rham_of_height_alteration : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.EigWholeDR.RamModelDR := by
  first | exact @GlobalTheory.TwoLat.ramModelDR | exact GlobalTheory.TwoLat.ramModelDR | (intros; apply GlobalTheory.TwoLat.ramModelDR <;> assumption)
