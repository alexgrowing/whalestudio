import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem sum_weightedHomogeneousComponent_image (f : MvPolynomial (Coord n) ℤ) :
    ∑ m ∈ f.support.image (Finsupp.weight (coordDeg n)), weightedHomogeneousComponent (coordDeg n) m f = f := by
  conv_rhs => rw [← sum_weightedHomogeneousComponent (coordDeg n) f]
  refine (finsum_eq_sum_of_support_subset _ ?_).symm
  intro m hm
  rw [Function.mem_support] at hm
  rw [Finset.coe_image, Set.mem_image]
  by_contra h
  refine hm (weightedHomogeneousComponent_eq_zero' m f fun d hd hdm ↦ h ⟨d, hd, hdm⟩)

theorem HomogGeneratorsExist.proof : HomogGeneratorsExist.Statement := by
  classical
  intro ι _ _ n P
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P.ideal : P.ideal.FG)

  let S : Finset (MvPolynomial (Coord n) ℤ) := s.biUnion fun f ↦
    (f.support.image (Finsupp.weight (coordDeg n))).image fun m ↦ weightedHomogeneousComponent (coordDeg n) m f
  have hShom : ∀ g ∈ S, ∃ m : ι → ℕ, IsWeightedHomogeneous (coordDeg n) g m := by
    intro g hg
    simp only [S, Finset.mem_biUnion, Finset.mem_image] at hg
    obtain ⟨f, -, m, -, rfl⟩ := hg
    exact ⟨m, weightedHomogeneousComponent_isWeightedHomogeneous m f⟩
  have hSP : ∀ g ∈ S, g ∈ P.ideal := by
    intro g hg
    simp only [S, Finset.mem_biUnion, Finset.mem_image] at hg
    obtain ⟨f, hf, m, -, rfl⟩ := hg
    exact P.homogeneous f (hs ▸ Ideal.subset_span hf) m
  let e := S.equivFin
  refine ⟨S.card, fun i ↦ (e.symm i : MvPolynomial (Coord n) ℤ),
    fun i ↦ Classical.choose (hShom _ (e.symm i).2), ⟨fun i ↦ Classical.choose_spec (hShom _ (e.symm i).2), ?_⟩⟩
  have hrange : Set.range (fun i ↦ (e.symm i : MvPolynomial (Coord n) ℤ)) = (S : Set _) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp⟩
  rw [hrange]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro g hg
    exact hSP g hg
  · rw [← hs, Ideal.span_le]
    intro f hf
    rw [← sum_weightedHomogeneousComponent_image f]
    refine Ideal.sum_mem _ fun m hm ↦ Ideal.subset_span ?_
    simp only [S, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image]
    exact ⟨f, hf, m, by simpa using hm, rfl⟩

end

end GroundTheory.Heights₂.Heights
