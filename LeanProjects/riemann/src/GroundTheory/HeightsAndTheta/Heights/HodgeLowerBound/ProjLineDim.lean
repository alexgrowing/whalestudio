import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsProjLineAmple
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped nonZeroDivisors

theorem ringKrullDim_mRing_line : ringKrullDim (MRing (PBlk 2)) = 3 := by
  have hZ : ringKrullDim ℤ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField
  have hc : Nat.card (Σ _ : Unit, PBlk 2 ()) = 2 := by simp
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hZ, hc]
  rfl

theorem eq_bot_of_isArithVar_line {W : Ideal (MRing (PBlk 2))} {d : ℕ} (hd : 1 ≤ d)
    (h : IsArithVar W (d + 1)) : W = ⊥ ∧ d = 1 := by
  obtain ⟨-, -, -, hdim⟩ := h
  simp only [Fintype.card_unit] at hdim
  by_cases hW : W = ⊥
  · refine ⟨hW, ?_⟩
    subst hW
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_mRing_line] at hdim
    have h3 : ((3 : ℕ) : WithBot ℕ∞) = ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := hdim
    have : (3 : ℕ) = d + 1 + 1 := by exact_mod_cast h3
    omega
  · exfalso
    obtain ⟨f, hfW, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have hnzd : f ∈ (MRing (PBlk 2))⁰ := mem_nonZeroDivisors_of_ne_zero hf0
    have hle := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk W) Ideal.Quotient.mk_surjective hnzd
      (Ideal.Quotient.eq_zero_iff_mem.mpr hfW)
    rw [hdim, ringKrullDim_mRing_line] at hle
    have h4 : ((d + 1 + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((3 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hle
    have : d + 1 + 1 + 1 ≤ 3 := by exact_mod_cast h4
    omega

end GroundTheory.Heights₂.Heights.LowerBoundFree
