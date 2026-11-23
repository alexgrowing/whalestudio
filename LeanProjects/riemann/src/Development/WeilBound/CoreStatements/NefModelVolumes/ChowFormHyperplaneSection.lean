import Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormOfIntegralVersion
import Development.WeilBound.CoreStatements.NefModelVolumes.HyperplaneSectionDivCycle
import Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormUniqueUpToConstant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly

open MvPolynomial

namespace ChowFormCompatibility

attribute [local instance] MvPolynomial.gradedAlgebra

theorem chow_form_hyperplane_section : GlobalTheory.Published.ChowFormHyperplaneSection := by
  unfold GlobalTheory.Published.ChowFormHyperplaneSection
  intro k _ _ N e P hP hprime _ u hu dl f hf d g hg
  have hrel : GroundTheory.Heights₂.Heights.IsRelevant P := by
    by_contra h
    simp only [GroundTheory.Heights₂.Heights.IsRelevant, not_exists, not_not] at h
    exact hu (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (h j))
  have hproj : GroundTheory.Heights₂.Heights.IsProjPrime P :=
    ⟨hprime, (GroundTheory.Heights₂.Heights.isHomogIdeal_iff P).2 hP, hrel⟩
  have hf' := chow_form_of_integral_version k N (e + 1) dl P f hf
  obtain ⟨c, hc, g', hg', heq⟩ :=
    GroundTheory.Heights₂.Heights.ChowFormSection.full k N (e + 1) P f u hproj hf' hu
  obtain ⟨hsec, hfix⟩ := hyperplane_section_divCycle k N (e + 1) P u f
  have key : ∀ Q ∈ (GroundTheory.Heights₂.Heights.divCycle P u).support,
      ∃ a : k, a ≠ 0 ∧ g' Q = C a * g Q := by
    intro Q hQ
    have hQ' : Q ∈ (GlobalTheory.ChowHt.hyperplaneSection P u).support := by
      rw [hsec]
      exact hQ
    exact chow_form_unique_up_to_constant k N (e + 1) Q (g Q) (g' Q) (chow_form_of_integral_version k N e (d Q) Q (g Q) (hg Q hQ')) (hg' Q hQ)
  choose! a ha hga using key
  refine ⟨c * ∏ Q ∈ (GroundTheory.Heights₂.Heights.divCycle P u).support, a Q ^ (GroundTheory.Heights₂.Heights.divCycle P u) Q, ?_, ?_⟩
  · exact mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun Q hQ => pow_ne_zero _ (ha Q hQ))
  · rw [hfix, heq, hsec, Finsupp.prod, map_mul, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun Q hQ => ?_
    rw [hga Q hQ, mul_pow, map_pow]

end ChowFormCompatibility
