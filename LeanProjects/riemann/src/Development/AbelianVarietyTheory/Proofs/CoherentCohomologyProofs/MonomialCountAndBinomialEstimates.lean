import Mathlib

namespace GlobalTheory

open Finset

theorem setOf_degree_eq_coe_finsuppAntidiag (σ : Type*) [Fintype σ] [DecidableEq σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a} = ↑(finsuppAntidiag (univ : Finset σ) a) := by
  ext α
  simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]

theorem ncard_degree_eq (σ : Type*) [Fintype σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a}.ncard = (a + Fintype.card σ - 1).choose a := by
  classical
  rw [setOf_degree_eq_coe_finsuppAntidiag, Set.ncard_coe_finset,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Nat.add_comm]

theorem ncard_degree_le (σ : Type*) [Fintype σ] (k : ℕ) :
    {α : σ →₀ ℕ | α.degree ≤ k}.ncard = (k + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  have hset : {α : σ →₀ ℕ | α.degree ≤ k} =
      ↑((range (k + 1)).biUnion fun a => finsuppAntidiag (univ : Finset σ) a) := by
    ext α
    simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion]
  · simp_rw [Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, ← Nat.multichoose_eq]
    exact Nat.sum_range_multichoose k _
  · intro a _ b _ hab
    exact Finset.disjoint_left.2 fun α h1 h2 =>
      hab ((Finset.mem_finsuppAntidiag.1 h1).1.symm.trans (Finset.mem_finsuppAntidiag.1 h2).1)

theorem natCard_degree_eq (σ : Type*) [Fintype σ] (a : ℕ) :
    Nat.card {α : σ →₀ ℕ // α.degree = a} = (a + Fintype.card σ - 1).choose a := by
  have h := ncard_degree_eq σ a
  rw [← Nat.card_coe_set_eq] at h
  exact h

theorem natCard_degree_le (σ : Type*) [Fintype σ] (k : ℕ) :
    Nat.card {α : σ →₀ ℕ // α.degree ≤ k} = (k + Fintype.card σ).choose (Fintype.card σ) := by
  have h := ncard_degree_le σ k
  rw [← Nat.card_coe_set_eq] at h
  exact h

theorem fintypeCard_degree_le (σ : Type*) [Fintype σ] (k : ℕ)
    [Fintype {α : σ →₀ ℕ // α.degree ≤ k}] :
    Fintype.card {α : σ →₀ ℕ // α.degree ≤ k} =
      (k + Fintype.card σ).choose (Fintype.card σ) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_degree_le σ k

end GlobalTheory
