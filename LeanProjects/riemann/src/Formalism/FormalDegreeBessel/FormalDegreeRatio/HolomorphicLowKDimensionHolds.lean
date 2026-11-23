import Formalism.FormalDegreeBessel.HolDimLowK
import Formalism.FormalDegreeBessel.FinalDS

open Finset

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

lemma prod_range_sub_cast_eq_factorial (b : ℕ) :
    ∏ j ∈ range b, ((b : ℝ) - (j : ℝ)) = (b.factorial : ℝ) := by
  have h := Finset.prod_range_reflect (fun j : ℕ => ((b : ℝ) - (j : ℝ))) b
  rw [← h, ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' : j < b := Finset.mem_range.mp hj
  have : ((b - 1 - j : ℕ) : ℝ) = (b : ℝ) - 1 - (j : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  rw [this]; ring

lemma prod_lt_sub_eq_factorial {n : ℕ} (b : Fin n) :
    ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      (((b : ℕ).factorial : ℕ) : ℝ) := by
  rw [Finset.prod_filter]
  have h1 : (∏ a : Fin n, (if a < b then (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) else 1)) =
      ∏ i ∈ range n, (if i < (b : ℕ) then (((b : ℕ) : ℝ) - (i : ℝ)) else 1) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => if i < (b : ℕ) then (((b : ℕ) : ℝ) - (i : ℝ)) else 1) n]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [Fin.lt_def]
  rw [h1, ← Finset.prod_filter]
  have h2 : (range n).filter (fun i => i < (b : ℕ)) = range (b : ℕ) := by
    ext i; simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨lt_trans h b.isLt, h⟩
  rw [h2, prod_range_sub_cast_eq_factorial]

theorem formal_degree_factorial_holds : FdegFactorial := by
  intro n
  have hswap : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) =
      ∏ b : Fin n, ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    simp_rw [Finset.prod_filter]
    exact Finset.prod_comm
  rw [hswap]
  simp_rw [prod_lt_sub_eq_factorial]
  exact Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℝ)) n

theorem formal_degree_dimension_holds : FdegDimV := by
  intro n lam hlam
  have hnum : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |lam a - lam b|) =
      ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b) := by
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
    exact abs_of_pos (sub_pos.mpr (hlam (Finset.mem_filter.mp hb).2))
  unfold fdegHC
  rw [hnum, formal_degree_factorial_holds n]

end Formalism.QuantumDeterminants
