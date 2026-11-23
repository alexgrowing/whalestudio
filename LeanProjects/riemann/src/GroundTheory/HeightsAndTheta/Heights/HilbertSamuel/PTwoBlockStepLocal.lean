import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockStepLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockPieceCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockCoeffCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockCycleExpand
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockStepLocal

theorem nonempty_of_isArithVar {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {x : Ix κ → Ω}
    (hX : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) : Nonempty κ := by
  by_contra h
  rw [not_nonempty_iff] at h
  have : IsEmpty (Σ k : Unit, GlobalTheory κ k) := ⟨fun p => h.false p.2⟩
  have h1 : ringKrullDim (MRing (GlobalTheory κ)) = 1 := by
    rw [ringKrullDim_mvPolynomial_of_isEmpty]
    exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField
  have h2 := ringKrullDim_quotient_le (coordIdeal ℤ x : Ideal (MRing (GlobalTheory κ)))
  rw [hX.2.2.2, h1] at h2
  have h3 : ((D + 1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := by simpa using h2
  have h4 := WithBot.coe_le_coe.1 h3
  norm_cast at h4

theorem choose_div_factorial {D i : ℕ} (hi : i ≤ D) (u : ℝ) :
    (D.choose i : ℝ) * u / (D.factorial : ℝ) = u / ((i.factorial : ℝ) * ((D - i).factorial : ℝ)) := by
  have e : ((D.choose i : ℕ) : ℝ) * (i.factorial : ℝ) * ((D - i).factorial : ℝ) = (D.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have h0 : (D.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
  have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((D - i).factorial : ℝ) ≠ 0 := by positivity
  rw [← e]
  field_simp

end TwoBlockStepLocal

open TwoBlockStepLocal in

theorem TwoBlockStepLocal.proof (hA : TwoBlockPieceCycle.Statement) (hM : TwoBlockCycleExpand.Statement)
    (hR : TwoBlockCoeffCycle.Statement) : TwoBlockStepLocal.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hB hm hm' hsp
  obtain ⟨c⟩ := nonempty_of_isArithVar hX
  obtain ⟨l, hl⟩ : ∃ l : Ix κ → ℤ, x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j := by
    have hc : x ⟨(), c⟩ ∈ Submodule.span ℤ (Set.range (matAct B x)) :=
      hsp (Submodule.subset_span ⟨⟨(), c⟩, rfl⟩)
    obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hc
    exact ⟨l, by rw [← hl]; simp [zsmul_eq_mul]⟩
  obtain ⟨a₀, C, h⟩ := hA D Ω κ x B c l hX hx hB hsp hl
  refine ⟨a₀, C, fun a b ha hb => ?_⟩
  convert h a b ha hb using 3
  rw [hM D Ω κ x B c l hX hx hB hsp hl a b, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiD : i ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [hR D Ω κ I x B m m' c l hI hX hx hB hm hm' hsp hl i hiD,
    show (D.choose i : ℝ) * (a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        twoBlockVert x (matAct B x) c l (twoBlockDegList D i) =
      (D.choose i : ℝ) * ((a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        twoBlockVert x (matAct B x) c l (twoBlockDegList D i)) by ring,
    choose_div_factorial hiD]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
