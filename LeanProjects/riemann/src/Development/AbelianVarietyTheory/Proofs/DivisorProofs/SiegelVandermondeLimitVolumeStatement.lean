import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelVandermondeLimitVolume
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_vandermonde_limit_volume : Hypotheses2 → HypothesesH → RegularAlteration → GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.Ch2HodgeVanishes → OnObj fun _ O _ _ _ _ => Tendsto (fun R : ℝ => sieg O.Y ∅ R - vdmVal O.Y R) atTop (𝓝 (O.Y.vol * bcFl O.Y)) := by
  first | exact @GlobalTheory.BcFib.tendsto_sieg_sub_vdmVal | exact GlobalTheory.BcFib.tendsto_sieg_sub_vdmVal | (intros; apply GlobalTheory.BcFib.tendsto_sieg_sub_vdmVal <;> assumption)
