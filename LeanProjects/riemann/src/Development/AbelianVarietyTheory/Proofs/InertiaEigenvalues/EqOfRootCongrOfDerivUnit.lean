import Mathlib
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem eq_of_root_congr_of_deriv_unit {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : Polynomial ℤ) (β β' : Ω)
    (hβ : A.valuation β ≤ 1) (hβ' : A.valuation β' ≤ 1) (h0 : Polynomial.aeval β f = 0) (h0' : Polynomial.aeval β' f = 0)
    (hd : ¬ A.valuation (Polynomial.aeval β (Polynomial.derivative f)) < 1) (hs : A.valuation (β - β') < 1) : β = β' := by
  by_contra hne
  have hb : β ∈ A := (A.valuation_le_one_iff β).mp hβ
  have hb' : β' ∈ A := (A.valuation_le_one_iff β').mp hβ'
  set b : A := ⟨β, hb⟩
  set b' : A := ⟨β', hb'⟩
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map (algebraMap ℤ A)) b (b' - b)
  rw [add_sub_cancel, derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap] at hk
  have hc := congrArg (fun x : A => (x : Ω)) hk
  have e : ∀ (p : ℤ[X]) (x : A), ((aeval x p : A) : Ω) = aeval (x : Ω) p := by
    intro p x
    exact (aeval_algebraMap_apply Ω x p).symm
  push_cast at hc
  rw [e, e, e] at hc
  have hβ0 : (b : Ω) = β := rfl
  have hβ1 : (b' : Ω) = β' := rfl
  rw [hβ0, hβ1, h0, h0'] at hc
  have hne' : β' - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hD : aeval β (derivative f) = -((k : Ω) * (β' - β)) := by
    have : (β' - β) * (aeval β (derivative f) + (k : Ω) * (β' - β)) = 0 := by linear_combination -hc
    have := (mul_eq_zero.mp this).resolve_left hne'
    linear_combination this
  apply hd
  rw [hD, Valuation.map_neg, Valuation.map_mul, Valuation.map_sub_swap]
  have hk1 : A.valuation (k : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr k.2
  calc A.valuation (k : Ω) * A.valuation (β - β') ≤ 1 * A.valuation (β - β') := by gcongr
    _ = A.valuation (β - β') := one_mul _
    _ < 1 := hs

end GlobalTheory
