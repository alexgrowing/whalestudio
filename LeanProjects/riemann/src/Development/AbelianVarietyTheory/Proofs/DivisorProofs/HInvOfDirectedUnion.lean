import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfFilteredColimitStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.UnionHInv

variable {A : Type} [CommRing A] {ι : Type} [Preorder ι] (S : ι → Subalgebra ℤ A) (hS : Monotone S)

noncomputable def diag : ι ⥤ CommRingCat.{0} where
  obj i := CommRingCat.of (S i)
  map {i j} h := CommRingCat.ofHom (Subalgebra.inclusion (hS (leOfHom h))).toRingHom
  map_id i := by ext x; rfl
  map_comp f g := by ext x; rfl

noncomputable def cocone : Cocone (diag S hS) where
  pt := CommRingCat.of A
  ι := { app := fun i => CommRingCat.ofHom (S i).val.toRingHom
         naturality := fun i j h => by ext x; rfl }

theorem cocone_isColimit [IsDirected ι (· ≤ ·)] [Nonempty ι] (hcov : ∀ a, ∃ i, a ∈ S i) :
    Nonempty (IsColimit (cocone S hS)) := by
  haveI : ReflectsColimitsOfShape ι (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change A at x
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · intro i j xi xj h
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, homOfLE hik, homOfLE hjk, ?_⟩
    apply Subtype.ext
    exact h

end GlobalTheory.UnionHInv

open GlobalTheory.UnionHInv in

theorem GlobalTheory.EtC.hInv_of_directed_union : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (S : ι → Subalgebra ℤ A), Monotone S → (∀ a, ∃ i, a ∈ S i) → (∀ i, IsUnit (q : S i)) → (∀ i, HInv q (S i)) → HInv q A := by
  intro q _ A _ ι _ _ _ S hS hcov hu hH
  obtain ⟨hc⟩ := cocone_isColimit S hS hcov
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_filtered_colimit q ι (diag S hS) (cocone S hS) hc hu hH
