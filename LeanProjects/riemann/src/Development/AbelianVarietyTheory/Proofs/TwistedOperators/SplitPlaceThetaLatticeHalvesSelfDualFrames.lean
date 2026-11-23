import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaxValuationIdealSplitPlaceAndConjugateStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameIntegStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPartMemCompletedSelfDualLatticeIffSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHomLatticeEntriesBoundedByIdealValuatiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBoundedMatrixFromHalfHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixHomLatticeBoundedConjugatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlaceBoundedMatrixFromConjugateHalfHomLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLatticeHalves

theorem splitLattice : ∀ D : D7, SplitLattice D := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he
  obtain ⟨⟨a, haA, ha0, hmax⟩, ⟨b, hbA, hb0, hbmax⟩⟩ := GlobalTheory.T.exists_max_valuation_ideal_splitPlace_and_conjugate D v φ e he
  refine ⟨⟨a, haA, ha0, hmax, Set.ext fun y => ⟨?_, fun hy => ?_⟩⟩,
    ⟨b, hbA, hb0, hbmax, Set.ext fun y => ⟨?_, fun hy => ?_⟩⟩⟩
  · rintro ⟨t, ⟨ht, -⟩, rfl⟩
    exact GlobalTheory.T.splitPlaceHomLattice_entries_bounded_by_idealValuation D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a hmax t ht
  · obtain ⟨u, hu, hh, rfl⟩ := GlobalTheory.T.splitPlaceBoundedMatrix_from_halfHomLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a haA ha0 y hy
    exact ⟨u, ⟨hu, hh⟩, rfl⟩
  · rintro ⟨t, ⟨ht, -⟩, rfl⟩
    exact GlobalTheory.T.splitPlaceAdjointMatrix_homLattice_bounded_conjugateIdeal D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he b hbmax t ht
  · obtain ⟨u, hu, hh, rfl⟩ := GlobalTheory.T.conjugatePlaceBoundedMatrix_from_conjugateHalfHomLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he b hbA hb0 y hy
    exact ⟨u, ⟨hu, hh⟩, rfl⟩

end GlobalTheory.SplitLatticeHalves
