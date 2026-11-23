import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArithKleiman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleiman
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ArithKleiman.trivial_hyps (P P0 : Ideal (MRing ι)) :
    ((constLine (ι := ι) 0).a = fun k => ((0 : K → ℕ) k : ℤ)) ∧ IsSemipositiveRel P0 P (constLine (ι := ι) 0) ∧
      MonomialsBounded P (constLine (ι := ι) 0) 0 ∧ IsConjInvariantH (constLine (ι := ι) 0) := by
  have hh : (constLine (ι := ι) 0).h = fun _ => 1 := by
    funext z
    show Real.exp (-0) = 1
    simp
  refine ⟨by funext k; rfl, ⟨?_, fun z _ w _ => ?_⟩, fun z _ μ hμ => ?_, fun z => by rw [hh]⟩
  · show ContDiffOn ℝ _ (fun _ => Real.exp (-(0 : ℝ))) _
    exact contDiffOn_const
  · have hf : (fun z => Real.log ((constLine (ι := ι) 0).h z)) = fun _ => (0 : ℝ) := by
      rw [hh]
      funext z
      simp
    rw [hf]
    simp [leviForm]
  · have h0 : ∀ p, μ p = 0 := by
      rintro ⟨k, i⟩
      have := hμ k
      simp only [Pi.zero_apply, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at this
      exact this i
    rw [hh]
    simp [h0]

theorem ArithKleiman.proof (hMix : MixedKleiman.Statement) : ArithKleiman.Statement := by
  intro K _ ι _ P P0 D A II hII hP hP0 hsemi hnef hconj hW
  obtain ⟨ha, hs, hm, hc⟩ := ArithKleiman.trivial_hyps (ι := ι) P P0
  have h := hMix K ι P P0 (D + 1) A (constLine 0) 0 II hII (Nat.succ_pos D) hP hP0 hsemi hnef hconj hW ha hs hm hc
    (D + 1) le_rfl
  have hl : (fun i : Fin (D + 1) => if (i : ℕ) < D + 1 then A else constLine 0) = fun _ => A :=
    funext fun i => if_pos i.isLt
  rwa [hl] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
