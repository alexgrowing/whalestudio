import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.IsoOfTrace

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.T.Alg.Trall

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Alg

variable (k : Type) [Field k] [CharZero k]

theorem sum_coeff_trace {n : ℕ} (x z : Matrix (Fin n) (Fin n) k) (p : k[X]) (hp : aeval x p = 0) (m : ℕ) :
    ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * trace (z * x ^ (m + i)) = 0 := by
  have h : trace (z * x ^ m * aeval x p) = 0 := by rw [hp, mul_zero, trace_zero]
  rw [aeval_eq_sum_range, Finset.mul_sum, trace_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, trace_smul, smul_eq_mul, mul_assoc, ← pow_add]

theorem trace_all_holds : TrAll k := by
  intro n Z x x' h z hz j
  have key : ∀ w : Z, ∀ j, j < 2 * n + 1 → trace ((w : Matrix (Fin n) (Fin n) k) * x ^ j) = trace ((w : Matrix (Fin n) (Fin n) k) * x' ^ j) := by
    intro w j hj
    have hw : (w : Matrix (Fin n) (Fin n) k) = ∑ i, (Module.finBasis k Z).repr w i • ((Module.finBasis k Z) i : Matrix (Fin n) (Fin n) k) := by
      nth_rewrite 1 [← (Module.finBasis k Z).sum_repr w]
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    rw [hw, Finset.sum_mul, Finset.sum_mul, trace_sum, trace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, trace_smul, trace_smul]
    congr 1
    exact congrFun h (⟨j, hj⟩, i)
  set q := x.charpoly * x'.charpoly with hqdef
  have hqm : q.Monic := x.charpoly_monic.mul x'.charpoly_monic
  have hdeg : q.natDegree = 2 * n := by
    rw [hqdef, x.charpoly_monic.natDegree_mul x'.charpoly_monic, charpoly_natDegree_eq_dim, charpoly_natDegree_eq_dim, Fintype.card_fin]
    ring
  have hx0 : aeval x q = 0 := by rw [hqdef, map_mul, aeval_self_charpoly, zero_mul]
  have hx'0 : aeval x' q = 0 := by rw [hqdef, map_mul, aeval_self_charpoly, mul_zero]
  have hrec : ∀ m, ∑ i ∈ Finset.range (2 * n + 1), q.coeff i * (trace (z * x ^ (m + i)) - trace (z * x' ^ (m + i))) = 0 := by
    intro m
    have h1 := sum_coeff_trace k x z q hx0 m
    have h2 := sum_coeff_trace k x' z q hx'0 m
    rw [hdeg] at h1 h2
    simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_zero]
  have hlead : q.coeff (2 * n) = 1 := by
    rw [← hdeg]
    exact hqm
  suffices hall : ∀ j, trace (z * x ^ j) - trace (z * x' ^ j) = 0 from sub_eq_zero.mp (hall j)
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < 2 * n + 1
    · exact sub_eq_zero.mpr (key ⟨z, hz⟩ j hj)
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 * n := ⟨j - 2 * n, by omega⟩
      have hm := hrec m
      rw [Finset.sum_range_succ, hlead, one_mul] at hm
      have hs : ∑ i ∈ Finset.range (2 * n), q.coeff i * (trace (z * x ^ (m + i)) - trace (z * x' ^ (m + i))) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [Finset.mem_range] at hi
          rw [ih (m + i) (by omega), mul_zero]
      rw [hs, zero_add] at hm
      exact hm

end PositivityTheory.RgUd.T.Alg.Trall
