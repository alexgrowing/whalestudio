import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlurisubharmonicOffBoundary
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plurisubharmonic_off_boundary : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c u, GlobalTheory.FlagPoly.Dom u → ∀ σ, PshOff ((T.M c).A σ) ((T.M c).Z σ) ((T.F c).th u σ + ReciprocityTheory.AnForm.M.LocPot.ofFun ((T.F c).ph u σ)) := by
  first | exact @GlobalTheory.HodgeWeightPos.pshOff_th_ph | exact GlobalTheory.HodgeWeightPos.pshOff_th_ph | (intros; apply GlobalTheory.HodgeWeightPos.pshOff_th_ph <;> assumption)
