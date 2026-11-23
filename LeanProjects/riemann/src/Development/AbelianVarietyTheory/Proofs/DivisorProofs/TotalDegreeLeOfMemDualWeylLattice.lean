import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.DualWeylDeg

theorem weight_colW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (t : Fin N) :
    (Finsupp.weight (colW N N) m) t = ∑ a : Fin N, m (a, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, colW, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp only [Pi.single_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb; simp; intro h; exact absurd h.symm hb
  · simp

theorem totalDegree_le_of_mem_dualWeyl : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O), f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := by
  intro O _ N ν f hf
  have h1 : f ∈ weightedHomogeneousSubmodule O (colW N N) ν := (Submodule.mem_inf.mp hf).1
  rw [mem_weightedHomogeneousSubmodule] at h1
  rw [totalDegree]
  refine Finset.sup_le fun m hm => ?_
  have h2 : Finsupp.weight (colW N N) m = ν := h1 (mem_support_iff.mp hm)
  have h3 : m.sum (fun _ e => e) = ∑ t, ∑ a : Fin N, m (a, t) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_comm]
  rw [h3]
  refine le_of_eq (Finset.sum_congr rfl fun t _ => ?_)
  rw [← weight_colW_apply, h2]

end GlobalTheory.DualWeylDeg
