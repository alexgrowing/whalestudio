import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBoundOfPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesCoverOfPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicityOfPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SRatOfIsotInternal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionToLocalLanglandsAStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionSeriesB0Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionSeriesB2Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SEta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitenessOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepsPin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterStatementAllStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotOverRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SXdAll
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem reductionStatements_of_casselmanWallach : GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.DiscreteSeriesUpqUnique → HypH → PrN → SerN →
    ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ArchCmp hL → PtSt hL →
    SA hL ∧ SMt ∧ SRat hL ∧ SCusp hL ∧ SettingsFormsExist hL ∧ SeriesExist hL ∧ SB2 hL ∧ SC hL ∧ SFin hL ∧
      ∀ cDep : ℝ, SettingsFormsExistList hL cDep ∧ SeriesExistList hL cDep ∧ ModuliPointsExistList hL cDep ∧ SFinl hL cDep := by
  intro hCW hHM hW hD hU hH hP hS hL hA hPt
  have hMt : SMt := GlobalTheory.T.multiplicity_of_primitive hP
  have hRat : SRat hL := GlobalTheory.HeightCounting.RatSide.sRat_of_duties hU hP hS (GlobalTheory.HeightCounting.Up.IsotAtStates.isot_allSt hW hD hH hP) hL
  have hPar : ParSt hL := GlobalTheory.T.parameter_statement_all hP hMt hL
  have hEta : SEta hL := GlobalTheory.StEta.sEta hP hL hPt
  have hFin := GlobalTheory.T.finiteness_of_localLanglands hW hD hP hL hA hEta (GlobalTheory.HeightCounting.Up.sXd_all hL)
  have hG := GlobalTheory.HeightCounting.UpPin.steps_pin hL 0
  refine ⟨GlobalTheory.T.reduction_to_local_langlands_A hP hA.pht hL, hMt, hRat, GlobalTheory.SCuspRows.sCusp_of_parSt hP hL hPar hRat, hG.1 (GlobalTheory.T.settingsFormsExistList_of_localLanglands hP hS hL 0),
    hG.2.1 (GlobalTheory.T.second_bound_of_primitive hP hS hL 0), hG.2.2.1 (GlobalTheory.T.moduliPointsExistList_of_localLanglands hP hS hL 0), GlobalTheory.T.series_cover_of_primitive hH.cover hCW hHM hP hS hL, hFin.1, fun c => ?_⟩
  exact ⟨GlobalTheory.T.settingsFormsExistList_of_localLanglands hP hS hL c, GlobalTheory.T.second_bound_of_primitive hP hS hL c, GlobalTheory.T.moduliPointsExistList_of_localLanglands hP hS hL c, hFin.2 c⟩

end GlobalTheory.HeightCounting.Up
