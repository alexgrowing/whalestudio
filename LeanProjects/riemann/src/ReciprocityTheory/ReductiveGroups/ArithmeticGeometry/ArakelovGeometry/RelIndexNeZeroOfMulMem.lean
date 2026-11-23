import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsMPrimeFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ChooseLePowDivFactorial

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Module

variable {Ω : Type} [Field Ω] [CharZero Ω]

theorem mul_mem_of_forall {S S' : Submodule ℤ Ω} {M : Ω} (hM : ∀ u ∈ S', M * u ∈ S) (A : Submodule ℤ Ω) :
    ∀ u ∈ A * S', M * u ∈ A * S := by
  intro u hu
  refine Submodule.mul_induction_on hu (fun a ha b hb => ?_) (fun y z hy hz => ?_)
  · rw [mul_left_comm]
    exact Submodule.mul_mem_mul ha (hM b hb)
  · rw [mul_add]
    exact add_mem hy hz

theorem relIndex_ne_zero_of_mul_mem {H K : Submodule ℤ Ω} (hK : K.FG) {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ u ∈ K, (M : Ω) * u ∈ H) : H.toAddSubgroup.relIndex K.toAddSubgroup ≠ 0 := by
  have hfg : AddGroup.FG K.toAddSubgroup :=
    (AddGroup.fg_iff_addSubgroup_fg _).mpr ((Submodule.fg_iff_addSubgroup_fg K).mp hK)
  have htor : IsAddTorsion (K.toAddSubgroup ⧸ H.toAddSubgroup.addSubgroupOf K.toAddSubgroup) := by
    intro q
    refine QuotientAddGroup.induction_on q fun u => ?_
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨M, hM0, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa [nsmul_eq_mul] using hM u u.2
  have := AddCommGroup.finite_of_fg_isAddTorsion _ htor
  exact AddSubgroup.index_ne_zero_of_finite

theorem relIndex_chain {G : Type*} [AddGroup G] (H : ℕ → AddSubgroup G) (n : ℕ)
    (hle : ∀ j < n, H j ≤ H (j + 1)) :
    ∀ k ≤ n, (H 0).relIndex (H k) = ∏ j ∈ Finset.range k, (H j).relIndex (H (j + 1)) ∧ H 0 ≤ H k
  | 0, _ => by simp [AddSubgroup.relIndex_self]
  | k + 1, hk => by
    obtain ⟨h1, h2⟩ := relIndex_chain H n hle k (by omega)
    refine ⟨?_, h2.trans (hle k (by omega))⟩
    rw [Finset.prod_range_succ, ← h1]
    exact (AddSubgroup.relIndex_mul_relIndex (hHK := h2) (hKL := hle k (by omega))).symm

variable {κ : Type} [Fintype κ]

theorem sec_zero' (x : κ → Ω) : sec ℤ x 0 = 1 := by
  unfold sec
  rw [← MvPolynomial.homogeneousSubmodule_one_pow (σ := κ) (R := ℤ) (n := 0), Submodule.map_pow, pow_zero]

theorem sec_one' (x : κ → Ω) : sec ℤ x 1 = Submodule.span ℤ (Set.range x) := by
  unfold sec
  simp [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
    Function.comp_def]

private theorem sec_eq_sec_one_pow (x : κ → Ω) (n : ℕ) : sec ℤ x n = sec ℤ x 1 ^ n := by
  unfold sec
  rw [← MvPolynomial.homogeneousSubmodule_one_pow (σ := κ) (R := ℤ) (n := n), Submodule.map_pow]

theorem log_relIndex_eq_sum (x x' : κ → Ω) (hle : sec ℤ x 1 ≤ sec ℤ x' 1)
    (hfin : ∃ M : ℕ, 0 < M ∧ ∀ s ∈ sec ℤ x' 1, (M : Ω) * s ∈ sec ℤ x 1) (n : ℕ) :
    Real.log ((sec ℤ x n).toAddSubgroup.relIndex (sec ℤ x' n).toAddSubgroup) =
      ∑ j ∈ Finset.range n,
      Real.log ((sec ℤ x (n - j) * sec ℤ x' j).toAddSubgroup.relIndex
        (sec ℤ x (n - j - 1) * sec ℤ x' (j + 1)).toAddSubgroup) := by
  obtain ⟨M, hM0, hM⟩ := hfin
  simp only [Nat.sub_sub]
  have hfgs : ∀ (y : κ → Ω) (k : ℕ), (sec ℤ y k).FG := fun y k => Module.Finite.iff_fg.mp inferInstance
  have e1 : ∀ j < n, sec ℤ x (n - j) = sec ℤ x (n - (j + 1)) * sec ℤ x 1 := by
    intro j hj
    rw [sec_eq_sec_one_pow x (n - j), sec_eq_sec_one_pow x (n - (j + 1)), ← pow_succ]
    congr 1
    omega
  have e2 : ∀ j, sec ℤ x' (j + 1) = sec ℤ x' j * sec ℤ x' 1 := by
    intro j
    rw [sec_eq_sec_one_pow x' (j + 1), sec_eq_sec_one_pow x' j, pow_succ]
  have hstep : ∀ j < n, sec ℤ x (n - j) * sec ℤ x' j ≤ sec ℤ x (n - (j + 1)) * sec ℤ x' (j + 1) := by
    intro j hj
    rw [e1 j hj, e2 j, mul_right_comm, ← mul_assoc]
    exact Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul ha (hle hb)
  have hne : ∀ j < n, (sec ℤ x (n - j) * sec ℤ x' j).toAddSubgroup.relIndex
      (sec ℤ x (n - (j + 1)) * sec ℤ x' (j + 1)).toAddSubgroup ≠ 0 := by
    intro j hj
    refine relIndex_ne_zero_of_mul_mem ((hfgs x _).mul (hfgs x' _)) hM0 fun u hu => ?_
    rw [e2 j, ← mul_assoc] at hu
    have h := mul_mem_of_forall hM (sec ℤ x (n - (j + 1)) * sec ℤ x' j) u hu
    rw [e1 j hj, mul_right_comm]
    exact h
  have chain := (relIndex_chain (fun j => (sec ℤ x (n - j) * sec ℤ x' j).toAddSubgroup) n
    (fun j hj => hstep j hj) n le_rfl).1
  simp only [Nat.sub_zero, Nat.sub_self, sec_zero', mul_one, one_mul] at chain
  rw [chain, Nat.cast_prod, Real.log_prod]
  intro j hj
  exact Nat.cast_ne_zero.mpr (hne j (Finset.mem_range.mp hj))

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
