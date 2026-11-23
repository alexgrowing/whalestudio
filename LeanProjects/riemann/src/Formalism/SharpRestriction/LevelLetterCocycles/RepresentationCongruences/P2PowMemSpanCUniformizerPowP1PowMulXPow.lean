import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FormalSeriesValueAtTwoPointsGenericPoints

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

namespace ContPA

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

section P2
variable {l : ℕ} [hlp : Fact l.Prime] {p1 p2 e u α β : O⟦X⟧}

theorem p1_pow_mem_span_C_pow_X_pow (hp : p1 = C (l : O) * e + u * X ^ l) (m η : ℕ) :
    p1 ^ m ∈ Ideal.span {C (l : O) ^ (m + 1 - (η + l - 1) / l), (X : O⟦X⟧) ^ η} := by
  have hl0 : 0 < l := hlp.out.pos
  have hle : η ≤ l * ((η + l - 1) / l) := by
    have h1 := Nat.div_add_mod (η + l - 1) l
    have h2 := Nat.mod_lt (η + l - 1) hl0
    omega
  have hsub : p1 - u * X ^ l ∈ Ideal.span {(C (l : O) : O⟦X⟧)} := by
    rw [hp, add_sub_cancel_right]
    exact Ideal.mem_span_singleton'.mpr ⟨e, mul_comm _ _⟩
  have h := pow_mem_span_of_sub hsub m ((η + l - 1) / l)
  refine mem_of_mem_span_pair h (Ideal.subset_span (by simp)) ?_
  have e1 : (u * X ^ l) ^ ((η + l - 1) / l) =
      (u ^ ((η + l - 1) / l) * X ^ (l * ((η + l - 1) / l) - η)) * (X : O⟦X⟧) ^ η := by
    rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  rw [e1]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem p2_sub_mul_X_pow_mem_span_C_natCast (hp : p1 = C (l : O) * e + u * X ^ l) (hp2 : p2 = C (l : O) * α + β * p1 ^ l) :
    p2 - β * (u ^ l * X ^ (l * l)) ∈ Ideal.span {(C (l : O) : O⟦X⟧)} := by
  have h1 : p1 - u * X ^ l = C (l : O) * e := by rw [hp]; ring
  have h2 : p1 ^ l - (u * X ^ l) ^ l ∈ Ideal.span {(C (l : O) : O⟦X⟧)} := by
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow p1 (u * X ^ l) l
    rw [hc, h1, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have e : p2 - β * (u ^ l * X ^ (l * l)) = C (l : O) * α + β * (p1 ^ l - (u * X ^ l) ^ l) := by
    rw [hp2]; ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    (Ideal.mul_mem_left _ _ h2)

variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

end P2

end ContPA

end Formalism.MainNotions.N.FrobeniusPowerSeries
