import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHodgeTateDifferenceKilled
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_hodge_tate_difference_killed : Hypotheses2 → HypothesesH → OnObj fun _ O _ _ _ _ => DeRhamHodgeTateDifferenceKilledAt O.Y := by
  first | exact @GlobalTheory.HTVert.onObj_aux1tAt_of_knownResults | exact GlobalTheory.HTVert.onObj_aux1tAt_of_knownResults | (intros; apply GlobalTheory.HTVert.onObj_aux1tAt_of_knownResults <;> assumption)
