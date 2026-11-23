import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamBaseGoodEmbedding
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_base_good_embedding : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → OnObj fun D O _ _ _ _ => 1 ≤ dimGr D.what₂.Tau O.N O.j ∧ ∀ c (M : DRBase O c), ∃ I : M.Emb, I.Good (genericPoint M.B) (dimGr D.what₂.Tau O.N O.j - 1) := by
  first | exact @GlobalTheory.BdDim.main | exact GlobalTheory.BdDim.main | (intros; apply GlobalTheory.BdDim.main <;> assumption)
