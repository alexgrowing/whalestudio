import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OfClassification
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MassRatioAllUnramifiedCmFields
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteSeriesThreeOfHyp

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory

theorem hypA_of_artinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCoverExists → GlobalTheory.Published.BesselUniquenessReal → GlobalTheory.Published.FormalDegreeCompactDual → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → HypA :=
fun ar cm we hm cd cw hf cl ce bu fd sw =>
  have c := GlobalTheory.DiscreteSeriesConsequences.of_classification cl
  have u : GlobalTheory.Published.DiscreteSeriesUpqUnique := GlobalTheory.Published.discreteSeriesUpqUnique_of_classification cl
  have d := GlobalTheory.discreteSeries_three_of_hypotheses ce c.2.2.2.2 u
  ⟨ar.rayClassFieldSt, ar.principalIdealSt, cm, hm, cd, cw, GlobalTheory.weilRepresentationUnitaryPair, c.2.2.1, hf, c.2.1, u,
    GlobalTheory.rowsFinDim_link, sw, GlobalTheory.BesselMapOne.besselMapUniq_of_besselUniqueness bu, c.2.2.2.2, fd, GlobalTheory.Mass.massRatio_all_unramified_cmFields,
    d.1, d.2.1, d.2.2, ar, we⟩

end GlobalTheory
