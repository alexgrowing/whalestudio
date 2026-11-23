import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TerminalChainOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasChainW
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
theorem _root_.GlobalTheory.T.terminal_chain_of_published_inputs : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd → TermWSt := by
  first | exact @GlobalTheory.PairTerm.termWSt_holds | exact GlobalTheory.PairTerm.termWSt_holds | (intros; apply GlobalTheory.PairTerm.termWSt_holds <;> assumption)
