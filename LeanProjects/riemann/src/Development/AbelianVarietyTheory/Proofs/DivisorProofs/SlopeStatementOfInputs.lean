import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesY
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeEqualitySlopeMeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamMinusHodgeTateGoodPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHodgeTateDifferenceKilledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvGradedReferenceLines
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.CovHt.SlopeTrue

theorem main : GlobalTheory.CovTop.HypothesesXH → HypothesesY → Hypotheses2 → HypothesesH → InputsSt → SlopeSt := by
  intro hX hY hP hH ⟨r, Cf, hI⟩
  obtain ⟨C, hC, h7⟩ := GlobalTheory.T.volume_equality_slope_mean r Cf
  refine ⟨C, hC, fun D O hc hf hb => ?_⟩
  obtain ⟨A, Φ, hh, hin⟩ := hI D O hc hf hb
  obtain ⟨A', T, H, ⟨rd⟩, -⟩ := GlobalTheory.Mean4O.ReadsEx.main hP.p4 D O hc
  exact h7 D O.Y hf (GlobalTheory.T.de_rham_minus_hodge_tate_good_primes hX hP hH hY.perfd D O hc hf A' T H rd) (GlobalTheory.T.de_rham_hodge_tate_difference_killed hP hH D O hc hf A' T H rd)
    (GlobalTheory.CompPropObj.main hP hH D O hc hf A' T H rd).2.2 hb A Φ hh hin

end GlobalTheory.CovHt.SlopeTrue
