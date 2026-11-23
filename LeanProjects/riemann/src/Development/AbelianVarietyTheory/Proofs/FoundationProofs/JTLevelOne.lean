import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem jT_invariant (γ : SL(2, ℤ)) (τ : ℍ) : jT (γ • τ) = jT τ :=
  ReciprocityTheory.ChartRestriction.L1.jT_smul γ τ

theorem DD_mul_jT_smul (γ : SL(2, ℤ)) (τ : ℍ) : DD τ * jT (γ • τ) = E₄ τ ^ 3 := by
  rw [jT_invariant, jT, ReciprocityTheory.ChartRestriction.L1.AA, mul_div_cancel₀ _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)]

theorem jT_level_one : ∀ E : Subring ℂ, Lv E 1 1 jT ∧ ∀ (γ : SL(2, ℤ)) (τ : ℍ), jT (γ • τ) = jT τ := by
  intro E
  refine ⟨⟨fun γ _ τ => jT_invariant γ τ, fun γ => ?_⟩, jT_invariant⟩
  have hE4 : QAll (· ∈ E) 1 ⇑E₄ := ((eis_q 1 one_pos _ (Or.inl rfl)).2.1) E
  have h3 : QAll (· ∈ E) 1 fun τ => E₄ τ ^ 3 := (QAllSubring.ring_closed E 1 one_pos).2.2.2.2.1 _ 3 hE4
  have hfun : (fun τ => DD τ ^ 1 * jT (γ • τ)) = fun τ => E₄ τ ^ 3 := by
    funext τ; rw [pow_one, DD_mul_jT_smul]
  rw [hfun]; exact h3

end GlobalTheory.FN
