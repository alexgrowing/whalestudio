import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesRationalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OntoXOfTwistSharesExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportFromReciprocityTheoremsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFromPageEstimate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PageEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankAtPlacesFromComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximumEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonOffTypePlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafShareIOfShareW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfSemilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankInfRangeAddInfKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadWStOfRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentEstimateFromLanglandsStatement
open GlobalTheory.BigOn

namespace GlobalTheory.BigOn

theorem ontoX_of_classicalTheorems : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.DiscreteSpectrumGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → OntoX := by
  intro hGreen hCoh hTemp hHecke hCheb hDisc hGal hBC hBS hAbove hDecay hLL hCover hCW
  have hArtin : GlobalTheory.Published.GlobalArtinReciprocity :=
    GlobalTheory.Published.HeckeLAdicCharacter.globalArtin hHecke
  have hRay : GlobalTheory.Published.RayClassFieldSt :=
    GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt hArtin
  have hSer : GlobalTheory.SerStd.SeriesRatS := (GlobalTheory.seriesRatS_and_serInt_of_globalArtin hArtin).1
  have hExport : ExportSt := by
    apply GlobalTheory.T.export_from_reciprocity_theorems <;> with_reducible assumption
  have hPage : PageSt := GlobalTheory.BigOn.pageSt
  have hGeo : GeoSt := GlobalTheory.BigOn.geoSt_of_pageSt hPage
  have hRank := GlobalTheory.BigOn.rankLocSt_of GlobalTheory.BigOn.maxSt hGeo GlobalTheory.BigOn.compareOffOwn_atRuns
  have hTwist : TwistSt := GlobalTheory.BigOn.TwistBoundAtPlace.twistSt_of hExport hGeo hRank
  have hModel := GlobalTheory.ShareOn.modelSt
  have hShare : ShareSt := GlobalTheory.ShareOn.shareSt_of_shareWSt (GlobalTheory.ShareOn.shareWSt_of_modelSt hModel)
  have hBad : BadSt := GlobalTheory.BigOn.badSt_of_badW (GlobalTheory.BadWOn.badWSt_of hGreen hModel)
  have hExp : ExpSt := GlobalTheory.T.exponent_estimate_from_langlands hCoh hTemp hHecke hCheb hDisc hGal hBC hBS hAbove hLL
  exact GlobalTheory.BigOn.ontoX_of_twist_shares_exp hExport hTwist hShare hBad hExp

end GlobalTheory.BigOn
