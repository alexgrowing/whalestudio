import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideExplicitIdentification
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4OfAdmittedTheoremII
import Formalism.SharpRestriction.GrowthBounds.PathWeight
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments
import Formalism.SharpRestriction.GrowthBounds.Joints
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.MainNotions.Pf14

theorem cleaning_of_admitted : ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ), tableLineDegreeFive.admitted D CLa Ck Crk Cdeg →
    SourceCleaning.aux₃ D C (C + 1) C := by
  obtain ⟨C, hC, H⟩ := Formalism.MainNotions.G.symbolGeneratorData.classMap_estimate_of_admissible
  refine ⟨C, hC, fun D CLa Ck Crk Cdeg hA => ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h15, h16, h17, h18, _, h20, h21, _⟩ := hA
  exact ⟨WittFrameLocaliserOrders.theta_kernel_expansion D, WittFrameLocaliserOrders.splitting_package_holds D, WittFrameLocaliserOrders.segment_statement_holds D, WittFrameLocaliserOrders.order_lemma_holds D,
    WittFrameLocaliserOrders.divisibility_of_field_lemma D h21, H D h15 h16 h17 h18 h20 h21⟩

theorem plane_gram_lemmas_of_admitted (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) : PlaneGramData.admitted D := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h11, _, h12, _, h14, h15, _, _, _, _, _, _, _, h23, h24, _⟩ := hA
  have hV : Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D := h12
  have hL52 : Formalism.MainNotions.CovariantDegrees.UnitProductSecondLemma D := h23
  have hL61 : Formalism.MainNotions.CovariantDegrees.DerivativeLemma D := h24
  exact ⟨Joints.isotypic_multiplicity_of_reducibility_alt D hV (GLWeightTheory.weight_condition_from_integral_form D),
    ⟨Joints.valuation_clauses_of_lattice_index D hL61.1, Joints.twisted_valuation_second_sentence D⟩,
    ⟨Joints.isotypic_coefficient_of_degree_bound D h14, Joints.third_degree_bound_gives_span_clause D h15, Joints.span_column_clauses D⟩,
    Joints.projection_of_integral_corollary D h11 hV.2 (GLWeightTheory.weight_condition_from_integral_form D), Joints.digit_identity_of_decomposition D hL52.1,
    Joints.derivation_of_lattice_index D hL61.2.1⟩

theorem plane_gram_of_admitted (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) {CH : ℝ} (hCH : 26 ≤ CH) :
    PlaneGramData.aux₃ D CH 2 24 60 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := plane_gram_lemmas_of_admitted D CLa Ck Crk Cdeg hA
  intro p O _ _ _ _ hSet
  exact Formalism.MainNotions.PlaneGram.stmt D hCH p O hSet
    ⟨a1 p O hSet, ⟨a2.1 p O hSet, a2.2 p O hSet⟩, ⟨a3.1 p O hSet, a3.2.1 p O hSet, a3.2.2 p O hSet⟩, a4 p O hSet,
      a5 p O hSet, a6 p O hSet⟩

theorem theorem_II_closed_of_test_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ), tableLineDegreeFive.admitted D CLa Ck Crk Cdeg →
    RemainingInputsAfter D CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60 → tableLineDegreeFive.ConclusionE D := by
  obtain ⟨C, hC, H⟩ := cleaning_of_admitted
  refine ⟨C, hC, fun D CLa Ck Crk Cdeg hA h6b => ?_⟩
  exact theorem_II_of_split_cloud_bounds D CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60 hA (H D CLa Ck Crk Cdeg hA)
    (plane_gram_of_admitted D CLa Ck Crk Cdeg hA le_rfl) (rest6a D CLa Ck Crk Cdeg) h6b

theorem stmtE_of_rests (D : Formalism.BasicNotions.D7)
    (h : ∀ CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ,
      RestCloudB D CLa Ck Crk Cdeg ∧ RestFlat D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ClosedFormOfAdmitted D := by
  obtain ⟨C, _, H⟩ := theorem_II_closed_of_test_bound
  intro CLa Ck Crk Cdeg hA
  obtain ⟨h1, h2⟩ := h CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60
  exact H D CLa Ck Crk Cdeg hA (test_bound_of_two_halves D CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60 h1 h2)

theorem stmtE_of_rest6b (D : Formalism.BasicNotions.D7)
    (h : ∀ CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ, RemainingInputsAfter D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    tableLineDegreeFive.ClosedFormOfAdmitted D := by
  obtain ⟨C, _, H⟩ := theorem_II_closed_of_test_bound
  intro CLa Ck Crk Cdeg hA
  exact H D CLa Ck Crk Cdeg hA (h CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60)

end Formalism.MainNotions.TestSideCounting
