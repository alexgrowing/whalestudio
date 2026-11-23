import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationUnconditional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrothendieckRingPolynomialOutright

namespace GlobalTheory

theorem geometricLemma_and_zelevinskyPolynomialRing :
    GlobalTheory.Published.GeometricLemma ∧ GlobalTheory.Published.ZelevinskyPolynomialRing :=
  ⟨GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds
               GlobalTheory.geometricLemmaFiltration_unconditional,
    GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.Laid.bzfin_holds
      GlobalTheory.segmentRepresentation' GlobalTheory.grothendieckRingPolynomial_outright⟩

end GlobalTheory
