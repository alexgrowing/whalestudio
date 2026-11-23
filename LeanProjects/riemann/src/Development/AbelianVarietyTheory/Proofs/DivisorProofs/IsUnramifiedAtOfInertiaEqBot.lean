import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem isUnramifiedAt_of_inertia_eq_bot (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsGalois K M] (P : Ideal (𝓞 M)) [P.IsPrime] (hP : P ≠ ⊥)
    (h : P.inertia (M ≃ₐ[K] M) = ⊥) : Algebra.IsUnramifiedAt (𝓞 K) P := by
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  haveI : (P.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) P
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (M ≃ₐ[K] M),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) (P.under (𝓞 K)) P, h]
  simp

end GlobalTheory
