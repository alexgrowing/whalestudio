import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTermTendstoZero
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
theorem _root_.GlobalTheory.T.archimedean_term_tendsto_zero : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → OnObj fun _ O _ _ _ _ => ∀ c (M : DRBase O c) (I : M.Emb) (z : M.B) (e m : ℕ) (s : (lbPow M.lamB m).Sec), I.Good z (e + 1) → I.Cuts s z e → Tendsto (fun R => M.arch R m s z e) atTop (𝓝 0) := by
  first | exact @GlobalTheory.ArchLim.arch_tendsto_zero | exact GlobalTheory.ArchLim.arch_tendsto_zero | (intros; apply GlobalTheory.ArchLim.arch_tendsto_zero <;> assumption)
