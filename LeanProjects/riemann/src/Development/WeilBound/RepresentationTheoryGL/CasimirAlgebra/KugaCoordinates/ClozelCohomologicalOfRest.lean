import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.GelfandValueOne.CasVal
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.TensorFormCoordinates.TensForm
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.TensorFormCoordinates.CoordConjAtEmb
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.EmbeddingConjugation.CoordConjEmbedding
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.FrameExistence.FrameHolds
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryTwistCoordinates.UnitTw
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.DeterminantDerivative.BigRep
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.MatrixConjugateSums.Summand
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinMapEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapSingleAtEmb
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Harmonic

namespace PositivityTheory.Rg.Cz

theorem clozelCohomological_of_rest (h1 : KType) (hgk : GKData) (hw : WhitLie) (hka : KugaAbs) (hkg : KugaGlue)
    (hcg : CoefGlue) (hco : Cochain) (hcb : CasBound) : GlobalTheory.Published.ClozelCohomological :=
  clozelCohomological_of h1 J.kData_holds hgk hw GlobalTheory.CompanionTheory.RgCz.charInt J.unitTw_holds
    (hcg hcb J.bigRep_holds J.bigCx_holds J.summand_holds hco J.casVal_holds)
    (hkg hka J.frame_holds GlobalTheory.CompanionTheory.FrameCasimir.frameCas J.cxExpand_holds J.tensForm_holds GlobalTheory.CompanionTheory.GKHarmonic.harmonic)

end PositivityTheory.Rg.Cz
