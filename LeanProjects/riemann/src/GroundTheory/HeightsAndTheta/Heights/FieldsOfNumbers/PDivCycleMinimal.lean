import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivCycleMinimal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContractedDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DivCycleMinimal.ringKrullDim_eq {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {F : Type u} [Field F] (Q : Ideal (MRing ι F)) (m : ℕ)
    (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MRing ι F ⧸ Q) = d := by
    have h2 := PFContracted.ringKrullDim_lt_top Q
    cases hc : ringKrullDim (MRing ι F ⧸ Q) with
    | bot =>
      rw [relDim, hc] at h
      exact absurd h (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        rw [hc] at h2
        exact absurd h2 (by simp)
      | coe d => exact ⟨d, rfl⟩
  rw [PFContracted.relDim_eq_int hd, PFContracted.natCast_withBot_withTop] at h
  have h' : (d : ℤ) - Fintype.card K = m := by
    have := WithBot.coe_injective h
    exact_mod_cast WithTop.coe_injective this
  rw [hd]
  congr 1
  omega

theorem DivCycleMinimal.proof : DivCycleMinimal.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hPn a ha W hW hWn hle
  have hmin : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨hW, hle⟩, fun Q hQ hQW => ?_⟩
    obtain ⟨hQp, hJQ⟩ := hQ
    by_contra hWQ
    obtain ⟨f, hfW, hfQ⟩ := Set.not_subset.mp hWQ
    have h1 := PFContracted.ringKrullDim_add_one_le (P := Q) (Q := W) hQW hfQ hfW
    have h2 := PFContracted.ringKrullDim_add_one_le (P := P) (Q := Q) (le_sup_left.trans hJQ) ha
      (hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
    have h3 := (add_le_add h1 (le_refl 1)).trans h2
    rw [DivCycleMinimal.ringKrullDim_eq W n hWn, DivCycleMinimal.ringKrullDim_eq P (n + 1) hPn] at h3
    have h4 : (((n + Fintype.card K + 1 + 1 : ℕ)) : WithBot ℕ∞) ≤ ((n + 1 + Fintype.card K : ℕ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using h3
    have h5 := WithBot.coe_le_coe.mp h4
    have h6 := ENat.natCast_le_natCast.mp h5
    omega
  exact ⟨hmin, length_localizedQuot_ne_top _ _ hmin⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
