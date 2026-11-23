import Development.EtaleCohomology.EtaleSheaves.LocalSlices

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 HomologicalComplex

namespace LateralTheory.E.LocSlicePf

def PullMono : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}),
  ((Over.forget X).sheafPullback (ModuleCat.{1} (ULift.{1} R)) (Scheme.etaleTopology.{0}.over X)
    Scheme.etaleTopology.{0}).PreservesMonomorphisms

theorem InjOver_of (hM : PullMono) : InjOver := by
  intro R _ X
  have := hM R X
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((Over.forget X).sheafAdjunctionContinuous (ModuleCat.{1} (ULift.{1} R)) (Scheme.etaleTopology.{0}.over X)
      Scheme.etaleTopology.{0})

theorem LocSlice_of' (hM : PullMono) : LateralTheory.E.LeafLocPf.LocSlice := LocSlice_of (InjOver_of hM)

end LateralTheory.E.LocSlicePf
