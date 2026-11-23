import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PublishedInputsImplyGalois
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfReadingStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoStOfPageSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankAtPlacesRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MaxSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompareOffOwnAtRuns
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistStOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareStOfShareWSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWStOfModelSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadStOfBadW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadWStOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExponentBoundOfUnitaryThetaStandardTheorems
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoXOfTwistSharesExp
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.BigOn
namespace GlobalTheory.BigOn
theorem ontoX_of_hypotheses_alt_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.GalS.CuspUAlt → _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.CuspRapidDecay → _root_.UpperTheory.Zero.LLC.RecTExists → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  intro hGreen hCoh hHecke hCheb hGal hBC hBS hAbove hDecay hLL hCover hCW
  have hArtin : GlobalTheory.Published.GlobalArtinReciprocity :=
    GlobalTheory.Published.HeckeLAdicCharacter.globalArtin hHecke
  have hRay : GlobalTheory.Published.RayClassFieldSt :=
    GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt hArtin
  have hSer : GlobalTheory.SerStd.SeriesRatS := (GlobalTheory.seriesRatS_and_serInt_of_globalArtin hArtin).1
  have hExport : _root_.GlobalTheory.BigOn.ExportedStatement := by
    apply _root_.GlobalTheory.T.exportSt_of_reciprocity_and_casselman_wallach <;> with_reducible assumption
  have hPage : _root_.GlobalTheory.BigOn.PageStatement := _root_.GlobalTheory.BigOn.pageSt_alt
  have hGeo : _root_.GlobalTheory.BigOn.GeometricStatement' := _root_.GlobalTheory.BigOn.geoSt_of_pageSt_alt hPage
  have hRank := _root_.GlobalTheory.BigOn.rankLocSt_of_max_geo_runs _root_.GlobalTheory.BigOn.maxSt_alt hGeo _root_.GlobalTheory.BigOn.compareOffOwn_atRuns_alt
  have hTwist : _root_.GlobalTheory.BigOn.TwistStatement' := _root_.GlobalTheory.BigOn.TwistBoundAtPlace.twistSt_of_alt hExport hGeo hRank
  have hModel := _root_.GlobalTheory.ShareOn.modelSt_alt
  have hShare : _root_.GlobalTheory.BigOn.ShareStatement := _root_.GlobalTheory.ShareOn.shareSt_of_shareWSt_alt (_root_.GlobalTheory.ShareOn.shareWSt_of_modelSt_alt hModel)
  have hBad : _root_.GlobalTheory.BigOn.BadPlacesStatement := _root_.GlobalTheory.BigOn.badSt_of_badW_alt (_root_.GlobalTheory.BadWOn.badWSt_of_greenCuspidal_of_modelSt hGreen hModel)
  have hExp : _root_.GlobalTheory.BigOn.ExponentStatement := _root_.GlobalTheory.T.expSt_of_base_change_and_crystalline_lattices hCoh hHecke hCheb hGal hBC hBS hAbove hLL
  exact _root_.GlobalTheory.BigOn.ontoX_of_twist_shares_exp_alt hExport hTwist hShare hBad hExp
end GlobalTheory.BigOn
end
end
