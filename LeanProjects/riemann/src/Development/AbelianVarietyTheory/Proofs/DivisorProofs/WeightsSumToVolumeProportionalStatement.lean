import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportional
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weights_sum_to_volume_proportional : Hypotheses2 → HypothesesH → OnObj fun _ O A T _ _ => (∀ c, (T.F c).Prop4 (A.w c)) ∧ O.Y.vol = ∑ c, A.w c ∧ Propor O.Y := by
  first | exact @GlobalTheory.CompPropObj.main | exact GlobalTheory.CompPropObj.main | (intros; apply GlobalTheory.CompPropObj.main <;> assumption)
