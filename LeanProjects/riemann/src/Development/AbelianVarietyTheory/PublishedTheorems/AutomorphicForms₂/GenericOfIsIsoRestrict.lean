import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.Published

open CategoryTheory AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.Published.generic_of_isIso_restrict {X X' : Scheme.{0}} [IsIntegral X]
    [IsIntegral X'] (π : X' ⟶ X) (U : X.Opens)
    (hU : (U : Set X).Nonempty) [IsIso (π ∣_ U)] :
    π (genericPoint X') = genericPoint X ∧ π.residueDegree (genericPoint X') = 1 := by
  have hrange : (U : Set X) ⊆ Set.range π := by
    intro y hy
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso ((π ∣_ U).base)).2 ⟨y, hy⟩
    refine ⟨x.1, ?_⟩
    have := congrArg Subtype.val hx
    simpa [morphismRestrict_base_coe] using this
  have hgen : π (genericPoint X') = genericPoint X := by
    have h1 := (genericPoint_spec X').image π.continuous
    have hdense : closure (Set.range π) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (U.isOpen.dense hU).closure_eq]
      exact closure_mono hrange
    rw [Set.image_univ, hdense] at h1
    exact h1.eq (genericPoint_spec X)
  refine ⟨hgen, ?_⟩
  have hmem : genericPoint X' ∈ π ⁻¹ᵁ U := by
    show π (genericPoint X') ∈ U
    rw [hgen]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  obtain ⟨x, hx⟩ : genericPoint X' ∈ Set.range (π ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]; exact hmem
  have h1 := _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp (π ∣_ U) U.ι x
  have h2 := _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp (π ⁻¹ᵁ U).ι π x
  rw [morphismRestrict_ι, h2, _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion (π ⁻¹ᵁ U).ι,
    _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion U.ι,
    _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion (π ∣_ U), hx] at h1
  simpa using h1

open CategoryTheory AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.Published.arBirational_of_arProj (H : _root_.GlobalTheory.Published.ArProj) :
    _root_.GlobalTheory.Published.ArBirational := by
  intro k _ X X' _ _ p p' D hp hp' _ _ π hπ U hU hiso L a hL
  obtain ⟨hgen, hdeg⟩ := _root_.GlobalTheory.Published.generic_of_isIso_restrict π U hU
  have := (H k X X' p p' D hp hp' π hπ hgen (by rw [hdeg]; exact one_ne_zero)).1 L a hL
  simpa [hdeg] using this

end GlobalTheory.Published
