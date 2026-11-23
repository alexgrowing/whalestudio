import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.TraceBinom

variable {R : Type} [Ring R] {n : ℕ}

theorem pow_succ_apply_path (M : Matrix (Fin n) (Fin n) R) (m : ℕ) (i j : Fin n) :
    (M ^ (m + 1)) i j = ∑ a : Fin m → Fin n,
      (List.ofFn fun l : Fin (m + 1) =>
        M ((Fin.cons i (Fin.snoc a j : Fin (m + 1) → Fin n) : Fin (m + 2) → Fin n) l.castSucc)
          ((Fin.cons i (Fin.snoc a j : Fin (m + 1) → Fin n) : Fin (m + 2) → Fin n) l.succ)).prod := by
  induction m generalizing i with
  | zero => simp; rfl
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ih x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [List.ofFn_succ, List.prod_cons]
    dsimp only [Fin.consEquiv, Equiv.coe_fn_mk]
    simp only [← Fin.cons_snoc_eq_snoc_cons, ← Fin.succ_castSucc, Fin.cons_succ,
      Fin.castSucc_zero, Fin.cons_zero]

theorem sum_cycWord_eq_trace (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    ∑ a : Fin (k + 1) → Fin n, ((cycWord a).map fun p => M p.1 p.2).prod = trace (M ^ (k + 1)) := by
  rw [Matrix.trace]
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, pow_succ_apply_path]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only [Fin.consEquiv, Equiv.coe_fn_mk]
  rw [cycWord, List.map_ofFn]
  congr 2
  funext l
  simp only [Function.comp_apply]
  rw [Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ]
  congr 1
  refine Fin.lastCases ?_ (fun l => ?_) l
  · simp
  · have e : finRotate (k + 1) l.castSucc = l.succ := by
      ext
      simp [Fin.val_add_one_of_lt (Fin.castSucc_lt_last l)]
    rw [e, Fin.cons_succ, Fin.snoc_castSucc]

theorem trace_add_algebraMap_pow [Algebra ℂ R] (M : Matrix (Fin n) (Fin n) R) (c : ℂ) (k : ℕ) :
    trace ((M + algebraMap ℂ (Matrix (Fin n) (Fin n) R) c) ^ (k + 1)) =
      algebraMap ℂ R (c ^ (k + 1) * n) + ∑ j ∈ range (k + 1),
        algebraMap ℂ R (((k + 1).choose (j + 1) : ℂ) * c ^ (k - j)) * trace (M ^ (j + 1)) := by
  rw [Commute.add_pow (Algebra.commute_algebraMap_right c M), Finset.sum_range_succ', trace_add, trace_sum,
    add_comm]
  congr 1
  · rw [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, ← map_pow, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.algebraMap_matrix_apply, if_true]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, map_mul, map_natCast, Nat.cast_comm]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hjk : k + 1 - (j + 1) = k - j := by omega
    have e : M ^ (j + 1) * algebraMap ℂ (Matrix (Fin n) (Fin n) R) c ^ (k + 1 - (j + 1)) *
        (((k + 1).choose (j + 1) : ℕ) : Matrix (Fin n) (Fin n) R) =
        (((k + 1).choose (j + 1) : ℂ) * c ^ (k - j)) • M ^ (j + 1) := by
      rw [hjk, ← map_pow, ← map_natCast (algebraMap ℂ (Matrix (Fin n) (Fin n) R)), mul_assoc, ← map_mul,
        ← Algebra.commutes, ← Algebra.smul_def, mul_comm (c ^ (k - j))]
    rw [e, trace_smul, Algebra.smul_def]

theorem trace_binomial : ∀ (R : Type) [Ring R] [Algebra ℂ R] (n : ℕ) (T : Fin n → Fin n → R) (c : ℂ) (k : ℕ), ∑ a : Fin (k + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2 + if p.1 = p.2 then algebraMap ℂ R c else 0)).prod = algebraMap ℂ R (c ^ (k + 1) * n) + ∑ j ∈ range (k + 1), algebraMap ℂ R (((k + 1).choose (j + 1) : ℂ) * c ^ (k - j)) * ∑ a : Fin (j + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2)).prod := by
  intro R _ _ n T c k
  have hA : (fun p : Fin n × Fin n => T p.1 p.2 + if p.1 = p.2 then algebraMap ℂ R c else 0) =
      fun p => (Matrix.of T + algebraMap ℂ (Matrix (Fin n) (Fin n) R) c) p.1 p.2 := by
    funext p
    simp [Matrix.algebraMap_matrix_apply]
  have hT : ∀ j : ℕ, ∑ a : Fin (j + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2)).prod =
      trace (Matrix.of T ^ (j + 1)) := fun j => sum_cycWord_eq_trace (Matrix.of T) j
  rw [hA, sum_cycWord_eq_trace, trace_add_algebraMap_pow]
  simp_rw [hT]

end GlobalTheory.TraceBinom
