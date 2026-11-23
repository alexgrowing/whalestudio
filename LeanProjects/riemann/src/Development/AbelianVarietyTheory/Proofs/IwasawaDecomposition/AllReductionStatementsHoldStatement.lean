import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllReductionStatementsHold
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.all_reduction_statements_hold : GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → HypH → PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ArchCmp hL → PtSt hL → SA hL ∧ SMt ∧ SRat hL ∧ SCusp hL ∧ SettingsFormsExist hL ∧ SeriesExist hL ∧ SB2 hL ∧ SC hL ∧ SFin hL ∧ ∀ cDep : ℝ, SettingsFormsExistList hL cDep ∧ SeriesExistList hL cDep ∧ ModuliPointsExistList hL cDep ∧ SFinl hL cDep := by
  first | exact @GlobalTheory.HeightCounting.Up.reductionStatements_of_casselmanWallach | exact GlobalTheory.HeightCounting.Up.reductionStatements_of_casselmanWallach | (intros; apply GlobalTheory.HeightCounting.Up.reductionStatements_of_casselmanWallach <;> assumption)
