import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapFlagDegreeIdentity
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_flag_degree_identity : Hypotheses2 → GlobalTheory.Published.ArDegree → ∀ G, Homog G → SwapFl G → ∀ (D : D7) (Y : DV.ShimX D.what₂.Tau) (hh : Fn Y), GlobalTheory.FlagZ.IsHh D.what₂.Tau Y.N hh → SwapEq Y G hh (degFl D.what₂.Tau Y.N) := by
  first | exact @GlobalTheory.CovTest.SwapZ.swapEq_flagZ | exact GlobalTheory.CovTest.SwapZ.swapEq_flagZ | (intros; apply GlobalTheory.CovTest.SwapZ.swapEq_flagZ <;> assumption)
