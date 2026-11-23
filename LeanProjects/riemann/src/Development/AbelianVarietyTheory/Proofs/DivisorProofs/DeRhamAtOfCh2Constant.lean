import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelVandermondeLimitVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeValueTendstoConstantStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR

theorem GlobalTheory.DeRhamValue.main : GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration →
    GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.Ch2HodgeVanishes → ∀ r : ℝ, Ch2Const r → OnObj fun _ O _ _ _ _ => DRAt O.Y r := by
  intro hS hX h2 hH hR hV r hr D O hc hf A T H h
  have ha : Tendsto (fun R : ℝ => sieg O.Y ∅ R - vdmVal O.Y R) atTop (𝓝 (O.Y.vol * bcFl O.Y)) :=
    (GlobalTheory.T.siegel_vandermonde_limit_volume) h2 hH hR hV D O hc hf A T H h
  have hb : Tendsto (vdmVal O.Y) atTop (𝓝 (-(2 * r * O.Y.vol * testI O.Y))) :=
    (GlobalTheory.T.vandermonde_value_tendsto_constant) hS hX h2 hH hR hV r hr D O hc hf A T H h
  have e := ha.add hb
  simp only [sub_add_cancel] at e
  unfold DRAt
  convert e using 2
  ring
