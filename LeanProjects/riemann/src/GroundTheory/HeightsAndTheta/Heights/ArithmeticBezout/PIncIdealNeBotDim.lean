import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncIdealNeBotDim
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Imports
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealNeBotDim.proof (h₁ : IncIdealDim.Statement) : IncIdealNeBotDim.Statement := by
  intro F _ n k Q hQ hI
  have := hQ.isPrime
  obtain ⟨j, -⟩ := hQ.isRelevant
  have hn : 0 < n := j.pos

  have hle : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((n : ℕ) : WithBot ℕ∞) := by
    have h := ringKrullDim_le_of_surjective (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((m : ℕ) : WithBot ℕ∞) := by
    have hbot : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = D at hle hbot ⊢
    induction D using WithBot.recBotCoe with
    | bot => exact absurd rfl hbot
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hle
        exact ENat.natCast_ne_top n (top_le_iff.mp (WithBot.coe_le_coe.mp h'))
      | coe m => exact ⟨m, rfl⟩
  have hm1 : 1 ≤ m := one_le_of_isProjPrime hQ hm
  rw [hm]
  by_contra hlt
  have hkm : k < m := by
    by_contra h
    exact hlt (by exact_mod_cast Nat.le_of_not_lt h)

  have hdim := h₁ F n k (m - 1) Q hQ (by rw [Nat.sub_add_cancel hm1]; exact hm)
  have hmin : min k (m - 1) = k := min_eq_left (by omega)
  have hkn : k ≤ k * n := Nat.le_mul_of_pos_right k hn
  rw [hmin, Nat.sub_add_cancel hkn] at hdim

  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hgnz : g ∈ nonZeroDivisors (MvPolynomial (Fin k × Fin n) F) := mem_nonZeroDivisors_of_ne_zero hg0
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hgnz
  have h3 : ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ incIdeal Q k) ≤
      ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ Ideal.span {g}) :=
    ringKrullDim_le_of_surjective
      (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem _).mpr hg))
      (Ideal.Quotient.factor_surjective _)
  have hS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_add]
  rw [hdim] at h3
  rw [hS] at h2
  have h4 : (((k * n : ℕ) : WithBot ℕ∞)) + 1 ≤ ((k * n : ℕ) : WithBot ℕ∞) :=
    le_trans (add_le_add h3 le_rfl) h2
  have h5 : ((k * n + 1 : ℕ) : WithBot ℕ∞) ≤ ((k * n : ℕ) : WithBot ℕ∞) := by exact_mod_cast h4
  have h6 : k * n + 1 ≤ k * n := by exact_mod_cast h5
  omega

end GroundTheory.Heights₂.Heights
