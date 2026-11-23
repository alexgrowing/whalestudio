import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Principalise

theorem comap_mul_idealSheaf : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (I J : X.IdealSheafData),
    (I * J).comap f = I.comap f * J.comap f := by
  intro X X' f I J
  have h : ∀ y : X', ∃ (U : X.affineOpens) (A : X'.affineOpens), y ∈ A.1 ∧ A.1 ≤ f ⁻¹ᵁ U.1 := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
    obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ f ⁻¹ᵁ U from hyU) (f ⁻¹ᵁ U).isOpen
    exact ⟨⟨U, hU⟩, ⟨A, hA⟩, hyA, hAU⟩
  choose U A hyA hAU using h
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top A ?_ fun y => ?_
  · exact top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyA y⟩
  · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, comapIdealAffine _ f (U y) (A y) (hAU y),
      comapIdealAffine _ f (U y) (A y) (hAU y), comapIdealAffine _ f (U y) (A y) (hAU y),
      Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

end GlobalTheory.Principalise
