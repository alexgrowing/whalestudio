import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitFamilyRelabel
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_family_relabel : Hypotheses2 → HypothesesH → OnObj fun _ O _ _ _ _ => ∀ Φ : ℝ → Fn O.Y, LimFam Φ → Relabel Φ := by
  first | exact @GlobalTheory.Mean4O.RelabelObj.relabel_onObj | exact GlobalTheory.Mean4O.RelabelObj.relabel_onObj | (intros; apply GlobalTheory.Mean4O.RelabelObj.relabel_onObj <;> assumption)
