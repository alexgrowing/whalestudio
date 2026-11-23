import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.EssSquareIntegrableSegmentsMain2
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.SegmentJacquetAllStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LanglandsMultisegmentsOfSeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentationStatement

namespace PositivityTheory.PfEss

theorem essSquareIntegrableSegments_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.EssSquareIntegrableSegments :=
  essSquareIntegrableSegments_main2 (PositivityTheory.Exh.langlandsExhaustionGL_of_seg hZ) PositivityTheory.Tls2.BZGL.standardFunctorsFiniteLength_top
    (fun k _ _ _ _ _ => PositivityTheory.Exh.lOrderFree_of (PositivityTheory.Exh.lUnlinkedIrr_of_seg hZ) k)
    (fun _ _ _ _ _ _ Δ => GlobalTheory.T.exists_segment_representation PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ)
    fun _ _ _ _ _ _ => GlobalTheory.T.segment_jacquet_all PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hZ

end PositivityTheory.PfEss
