import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.HeadSeg
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation

namespace PositivityTheory.Groth

theorem grothendieckRingPolynomial_holds : GlobalTheory.Published.GrothendieckRingPolynomial :=
  grothendieckRingPolynomial_of_seg PositivityTheory.RgGu.segmentRepresentation

theorem lUnlinkedIrr_holds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZSeg.LUnlinkedIrr k := PositivityTheory.Exh.lUnlinkedIrr_of_seg PositivityTheory.RgGu.segmentRepresentation k

end PositivityTheory.Groth
