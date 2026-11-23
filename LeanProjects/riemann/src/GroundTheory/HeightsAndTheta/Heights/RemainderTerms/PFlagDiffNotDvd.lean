import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagDiffNotDvd.proof : FlagDiffNotDvd.Statement := by
  intro σ _ a b c d hab hcd h1 h2 hdvd
  let ψ : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
    aeval (fun i => X (if i = a then b else i))
  have hψ : ∀ i, ψ (X i) = X (if i = a then b else i) := fun i => by
    simp only [ψ, aeval_X]
  obtain ⟨q, hq⟩ := hdvd
  have h := congrArg ψ hq
  rw [map_mul, map_sub, map_sub, hψ, hψ, hψ, hψ, if_pos rfl, if_neg (Ne.symm hab), sub_self,
    zero_mul, sub_eq_zero] at h
  have hcd' := X_injective h
  by_cases hc : c = a <;> by_cases hd : d = a
  · exact hcd (hc.trans hd.symm)
  · rw [if_pos hc, if_neg hd] at hcd'
    exact h1 ⟨hc.symm, hcd'⟩
  · rw [if_neg hc, if_pos hd] at hcd'
    exact h2 ⟨hd.symm, hcd'.symm⟩
  · rw [if_neg hc, if_neg hd] at hcd'
    exact hcd hcd'

end RestTerms

end GroundTheory.Heights₂.Heights
