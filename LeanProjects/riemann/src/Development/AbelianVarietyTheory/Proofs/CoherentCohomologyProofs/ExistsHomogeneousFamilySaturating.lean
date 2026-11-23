import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in

theorem _root_.GlobalTheory.exists_homogeneous_family_saturating : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ], (∀ i : ι, ∃ T : Finset M, ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M)) → ∃ (r : ℕ) (d : Fin r → ℤ) (g : Fin r → M), (∀ l, g l ∈ ℳ (d l)) ∧ ∀ (i : ι) (y : M), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (Set.range g) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ hT
  choose T hT using hT
  choose S hS using fun m : M => _root_.GlobalTheory.exists_sum_grProj ℳ m
  classical
  let G : Finset (ℤ × M) := (Finset.univ.biUnion T).biUnion fun t =>
    (S t).image fun j => (j, _root_.GlobalTheory.GradedHilbert.proj ℳ j t)
  refine ⟨G.card, fun l => (G.equivFin.symm l).1.1, fun l => (G.equivFin.symm l).1.2,
    fun l => ?_, fun i y => ?_⟩
  · have hmem := (G.equivFin.symm l).2
    obtain ⟨t, -, hj⟩ := Finset.mem_biUnion.1 hmem
    obtain ⟨j, -, hjeq⟩ := Finset.mem_image.1 hj
    show (G.equivFin.symm l : ℤ × M).2 ∈ ℳ (G.equivFin.symm l : ℤ × M).1
    rw [← hjeq]
    exact _root_.GlobalTheory.GradedHilbert.proj_mem ℳ j t
  · obtain ⟨k, hk⟩ := hT i y
    refine ⟨k, Submodule.span_le.2 ?_ hk⟩
    intro t ht
    rw [← hS t]
    refine Submodule.sum_mem _ fun j hj => Submodule.subset_span ?_
    have hG : (j, _root_.GlobalTheory.GradedHilbert.proj ℳ j t) ∈ G :=
      Finset.mem_biUnion.2 ⟨t, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩,
        Finset.mem_image.2 ⟨j, hj, rfl⟩⟩
    exact ⟨G.equivFin ⟨_, hG⟩, by simp⟩

end GlobalTheory
