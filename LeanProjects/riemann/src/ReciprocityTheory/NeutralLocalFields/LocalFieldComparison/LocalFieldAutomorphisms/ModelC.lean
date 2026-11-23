import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Inertia

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

attribute [local instance] locRel

theorem norm_le_one_of_monic_root (P : Polynomial (PadicAlgCl p)) (hP : P.Monic) (hc : ∀ i, ‖P.coeff i‖ ≤ 1)
    {x : PadicAlgCl p} (hx : P.eval x = 0) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have key : ∀ m, ‖∑ i ∈ Finset.range (m + 1), P.coeff i * x ^ i‖ ≤ ‖x‖ ^ m := by
    intro m
    induction m with
    | zero => simpa using hc 0
    | succ m ih =>
      rw [Finset.sum_range_succ]
      refine (norm_add_le_max_padic _ _).trans (max_le ?_ ?_)
      · exact ih.trans (pow_le_pow_right₀ hlt.le (Nat.le_succ m))
      · rw [norm_mul, norm_pow]
        calc ‖P.coeff (m + 1)‖ * ‖x‖ ^ (m + 1) ≤ 1 * ‖x‖ ^ (m + 1) := by gcongr; exact hc _
          _ = ‖x‖ ^ (m + 1) := one_mul _
  have he := P.eval_eq_sum_range (x := x)
  rw [hx] at he
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
  · rw [h0] at he
    simp [hP.coeff_natDegree ▸ (show P.coeff 0 = P.coeff P.natDegree by rw [h0])] at he
  · obtain ⟨m, hm⟩ : ∃ m, P.natDegree = m + 1 := ⟨P.natDegree - 1, by omega⟩
    rw [hm, Finset.sum_range_succ, ← hm, hP.coeff_natDegree, one_mul, hm] at he
    have e2 : x ^ (m + 1) = -∑ i ∈ Finset.range (m + 1), P.coeff i * x ^ i := by
      linear_combination -he
    have := key m
    rw [← norm_neg, ← e2, norm_pow] at this
    have h3 : ‖x‖ ^ m < ‖x‖ ^ (m + 1) := pow_lt_pow_right₀ hlt (Nat.lt_succ_self m)
    linarith

example (ι : Ω →+* PadicAlgCl p) : algebraMap 𝒪[Kloc F ι] (AlgebraicClosure (Kloc F ι)) =
    (algebraMap (Kloc F ι) (AlgebraicClosure (Kloc F ι))).comp (algebraMap 𝒪[Kloc F ι] (Kloc F ι)) := rfl

end ReciprocityTheory.Neutral.Cmp
