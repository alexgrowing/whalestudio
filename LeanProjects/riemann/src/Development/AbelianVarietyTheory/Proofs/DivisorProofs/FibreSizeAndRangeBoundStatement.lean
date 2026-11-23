import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSizeAndRangeBound
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_size_and_range_bound : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c, (T.F c).Size ∧ (T.F c).InR O.Y.j := by
  first | exact @GlobalTheory.InterpMetricObj.size_inR | exact GlobalTheory.InterpMetricObj.size_inR | (intros; apply GlobalTheory.InterpMetricObj.size_inR <;> assumption)
