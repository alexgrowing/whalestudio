import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockFnField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem TwoBlockFnField.ratio_mem {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (p q : Ix κ) : x p / x q ∈ blockFnField (ι := GlobalTheory κ) x :=
  IntermediateField.subset_adjoin ℚ _ ⟨p, q, Subsingleton.elim _ _, rfl⟩

theorem TwoBlockFnField.matAct_le {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (A : Matrix (Ix κ) (Ix κ) ℚ) :
    blockFnField (ι := GlobalTheory κ) (matAct A x) ≤ blockFnField (ι := GlobalTheory κ) x := by
  rw [blockFnField, IntermediateField.adjoin_le_iff]
  rintro t ⟨p, q, -, rfl⟩
  by_cases h0 : ∀ j, x j = 0
  · have : matAct A x p = 0 := by simp [matAct, h0]
    rw [this, zero_div]
    exact zero_mem _
  · obtain ⟨c, hc⟩ := not_forall.mp h0
    have key : ∀ i, matAct A x i / x c ∈ blockFnField (ι := GlobalTheory κ) x := by
      intro i
      have : matAct A x i / x c = ∑ j, (A i j : Ω) * (x j / x c) := by
        simp only [matAct, Finset.sum_div, mul_div_assoc]
      rw [this]
      refine sum_mem fun j _ => mul_mem ?_ (TwoBlockFnField.ratio_mem x j c)
      simp
    have : matAct A x p / matAct A x q = (matAct A x p / x c) / (matAct A x q / x c) := by
      rw [div_div_div_cancel_right₀ hc]
    rw [this]
    exact div_mem (key p) (key q)

theorem TwoBlockFnField.matAct_eq {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (hB : IsInvMat B) :
    blockFnField (ι := GlobalTheory κ) (matAct B x) = blockFnField (ι := GlobalTheory κ) x := by
  classical
  obtain ⟨B', -, h⟩ := isInvMat_mul hB
  refine le_antisymm (TwoBlockFnField.matAct_le x B) ?_
  have := TwoBlockFnField.matAct_le (matAct B x) B'
  rwa [matAct_matAct h] at this

theorem TwoBlockFnField.proof : TwoBlockFnField.Statement := by
  intro Ω _ _ κ _ x B hB
  have hE := TwoBlockFnField.matAct_eq x B hB
  refine ⟨le_antisymm ?_ ?_, hE⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    obtain ⟨b, i⟩ := p
    obtain ⟨b', j⟩ := q
    simp only at hpq
    subst hpq
    by_cases hb : b = 0
    · subst hb
      simpa [pair] using TwoBlockFnField.ratio_mem x ⟨(), i⟩ ⟨(), j⟩
    · simp only [pair, hb, if_false]
      rw [← hE]
      exact TwoBlockFnField.ratio_mem (matAct B x) ⟨(), i⟩ ⟨(), j⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨⟨u, i⟩, ⟨u', j⟩, -, rfl⟩
    cases u; cases u'
    refine IntermediateField.subset_adjoin ℚ _ ⟨⟨0, i⟩, ⟨0, j⟩, rfl, ?_⟩
    simp [pair]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
