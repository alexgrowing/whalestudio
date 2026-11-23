import Mathlib

universe u_1

namespace GlobalTheory.IrreducibleGeneralizations

open AlgebraicGeometry Topology

theorem isIrreducible_generalizations {X : Scheme.{u_1}} (x : X) [IsDomain (X.presheaf.stalk x)] :
    IsIrreducible {y : X | y ⤳ x} := by

  have hSpec : IsIrreducible (Set.univ : Set (PrimeSpectrum (X.presheaf.stalk x))) :=
    IrreducibleSpace.isIrreducible_univ _
  rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
  exact hSpec.image _ (X.fromSpecStalk x).continuous.continuousOn

theorem component_eq_closure {X : Scheme.{u_1}} {x : X} [IsDomain (X.presheaf.stalk x)]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hx : x ∈ Z) :
    Z = closure {y : X | y ⤳ x} := by

  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hsub : Z ⊆ closure {y : X | y ⤳ x} := fun z hz =>
    closure_mono (Set.singleton_subset_iff.mpr (hη.specializes hx)) (hη.specializes hz).mem_closure
  exact hsub.antisymm (hZ.2 (isIrreducible_generalizations x).closure hsub)

theorem main : ∀ {X : AlgebraicGeometry.Scheme} {x : ↥X} [IsDomain (↑(TopCat.Presheaf.stalk (AlgebraicGeometry.PresheafedSpace.presheaf (AlgebraicGeometry.SheafedSpace.toPresheafedSpace (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace (AlgebraicGeometry.Scheme.toLocallyRingedSpace X)))) x) : Type u_1)] {Z W : Set ↥X}, Z ∈ irreducibleComponents ↥X → W ∈ irreducibleComponents ↥X → x ∈ Z → x ∈ W → Z = W := by
  intro X x _ Z W hZ hW hxZ hxW
  rw [component_eq_closure hZ hxZ, component_eq_closure hW hxW]

end GlobalTheory.IrreducibleGeneralizations
