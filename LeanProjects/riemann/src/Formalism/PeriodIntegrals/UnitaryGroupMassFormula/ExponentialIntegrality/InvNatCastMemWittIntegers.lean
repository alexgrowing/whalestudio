import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.Development

noncomputable section

namespace PI.ExpIntWProof

open PI

theorem norm_p (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have e : (p : ℂ_[p]) = ((algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    simp
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  first
  | exact Padic.norm_p
  | simp [Padic.norm_p]

theorem norm_intCast_le_one (p : ℕ) [Fact p.Prime] (t : ℤ) : ‖(t : ℂ_[p])‖ ≤ 1 := by
  exact IsUltrametricDist.norm_intCast_le_one ℂ_[p] t

theorem p_mem (p : ℕ) [Fact p.Prime] : (p : ℂ_[p]) ∈ Wp p := natCast_mem _ p

theorem inv_mem_of_norm_sub_lt (p : ℕ) [Fact p.Prime] {x : ℂ_[p]} (hx : x ∈ Wp p)
    (h : ‖1 - x‖ < 1) : x⁻¹ ∈ Wp p := by
  have hs : HasSum (fun n : ℕ => (1 - x) ^ n) (1 - (1 - x))⁻¹ := hasSum_geometric_of_norm_lt_one h
  rw [sub_sub_cancel] at hs
  have hcl : IsClosed (Wp p : Set ℂ_[p]) := Subring.isClosed_topologicalClosure _
  refine hcl.mem_of_tendsto hs.tendsto_sum_nat (Filter.Eventually.of_forall fun n => ?_)
  exact Subring.sum_mem _ fun i _ => pow_mem (sub_mem (one_mem _) hx) i

theorem inv_natCast_mem_wittIntegers (p : ℕ) [hp : Fact p.Prime] (u : ℕ) (hu : ¬ p ∣ u) :
    ((u : ℂ_[p]))⁻¹ ∈ Wp p := by
  have hcop : Nat.Coprime u p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu).symm
  have hb := Nat.gcd_eq_gcd_ab u p
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  set a : ℤ := Nat.gcdA u p
  set b : ℤ := Nat.gcdB u p
  set y : ℂ_[p] := (u : ℂ_[p]) * (a : ℂ_[p]) with hy
  have h1y : 1 - y = (p : ℂ_[p]) * (b : ℂ_[p]) := by
    have := congrArg (fun z : ℤ => (z : ℂ_[p])) hb
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast] at this
    rw [hy, this]
    ring
  have hlt : ‖1 - y‖ < 1 := by
    rw [h1y, norm_mul, norm_p]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    calc (p : ℝ)⁻¹ * ‖(b : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (norm_intCast_le_one p b) (by positivity)
      _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hp1
  have hyW : y ∈ Wp p := mul_mem (natCast_mem _ u) (intCast_mem _ a)
  have hyinv := inv_mem_of_norm_sub_lt p hyW hlt
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, sub_zero, norm_one] at hlt
    exact lt_irrefl _ hlt
  have ha0 : (a : ℂ_[p]) ≠ 0 := fun h0 => hy0 (by rw [hy, h0, mul_zero])
  have hu0 : (u : ℂ_[p]) ≠ 0 := fun h0 => hy0 (by rw [hy, h0, zero_mul])
  have : ((u : ℂ_[p]))⁻¹ = (a : ℂ_[p]) * y⁻¹ := by
    rw [hy]
    field_simp
  rw [this]
  exact mul_mem (intCast_mem _ a) hyinv

end PI.ExpIntWProof

end
