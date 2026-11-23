import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentGenericOfJacquetNuPairStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedProductIrreducibleAltBis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoSegmentGenericSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReorderOfUnlinkedCommuteSwapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentationStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.SegmentJacquetAllStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerRankHeredity.ProdFL
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerRankHeredity.WhitStd
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.NuPair
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SwapProducts.SwapProd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.RgGu

theorem whitRankIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.WhitRankIrr k :=
  fun k _ _ _ _ => PositivityTheory.rg.gu.whit.whitRankIrr k

theorem whitRankStd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.WhitRankStd k :=
  fun k _ _ _ _ => whitRankStd_of_heredity k (GlobalTheory.T.whittaker_heredity k) (whitRankIrr k)

theorem lSegJacquet (hZ : GlobalTheory.Published.SegmentRepresentation) : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSegJacquet k :=
  fun _ _ _ _ _ => GlobalTheory.TL.segment_jacquet_all irreducibleAdmissibleGL hZ

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.NuPair k :=
  fun k _ _ _ _ => GlobalTheory.RgGu.Nup2.nuPair k

theorem lUnlinkedIrr (hZ : GlobalTheory.Published.SegmentRepresentation) : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedIrr k :=
  fun k _ _ _ _ => GlobalTheory.T.lUnlinkedIrr_of_irreducibleAdmissible k irreducibleAdmissibleGL (lSegJacquet hZ k) PositivityTheory.Geo.geometricLemmaFiltration
    (nuPair k) (whitRankStd k) (prodIrrFiniteLength k)

theorem reorder (hZ : GlobalTheory.Published.SegmentRepresentation) : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.Reorder k :=
  fun k _ _ _ _ => GlobalTheory.T.reorder_of_unlinked_commute_swap k (GlobalTheory.T.unlinked_commute_of_irreducible k irreducibleAdmissibleGL (lUnlinkedIrr hZ k)) (GlobalTheory.RgGu.Swap.swapProd k)

end GlobalTheory.RgGu

end
