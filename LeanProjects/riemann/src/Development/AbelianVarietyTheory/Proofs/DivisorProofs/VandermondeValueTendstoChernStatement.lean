import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeValueTendstoChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR
theorem _root_.GlobalTheory.T.vandermonde_value_tendsto_chern : GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.Ch2HodgeVanishes → ∀ r : ℝ, Ch2Const r → OnObj fun D O _ _ _ _ => Tendsto (vdmVal O.Y) atTop (𝓝 (r * O.Y.chern (lamA D.what₂.Tau O.Y.N O.Y.j ^ dimGr D.what₂.Tau O.Y.N O.Y.j * vdmCl D.what₂.Tau O.Y.N O.Y.j))) := by
  first | exact @GlobalTheory.VdmCore.tendsto_vdmVal | exact GlobalTheory.VdmCore.tendsto_vdmVal | (intros; apply GlobalTheory.VdmCore.tendsto_vdmVal <;> assumption)
