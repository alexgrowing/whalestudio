import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowEntryCommutator
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

section GelfandCentral

variable {A : Type} [Ring A] {n : ℕ}

theorem sum_fin_succ_fun_cons {M : Type} [AddCommMonoid M] (k : ℕ) (f : (Fin (k + 1) → Fin n) → M) :
    ∑ idx, f idx = ∑ c : Fin n, ∑ idx : Fin k → Fin n, f (Fin.cons c idx) := by
  rw [← Fintype.sum_prod_type']
  exact ((Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp f).symm

theorem pow_of_apply_eq_sum_paths (E : Fin n → Fin n → A) (k : ℕ) (c e : Fin n) :
    (Matrix.of E ^ (k + 1)) c e = ∑ idx : Fin k → Fin n, (List.ofFn fun a : Fin (k + 1) =>
      E ((Fin.cons c idx : Fin (k + 1) → Fin n) a) ((Fin.snoc idx e : Fin (k + 1) → Fin n) a)).prod := by
  induction k generalizing c with
  | zero => simp [Fin.snoc]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, sum_fin_succ_fun_cons]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [List.ofFn_succ (n := k + 1), List.prod_cons, ← Fin.cons_snoc_eq_snoc_cons]
    simp

theorem gelfA_eq_sum_pow (E : Fin n → Fin n → A) (k : ℕ) :
    gelfA E k = ∑ c, (Matrix.of E ^ (k + 1)) c c := by
  rw [gelfA, sum_fin_succ_fun_cons]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pow_of_apply_eq_sum_paths]
  refine Finset.sum_congr rfl fun idx _ => ?_
  congr 2
  funext a
  congr 1
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp
  · rw [Fin.coeSucc_eq_succ]; simp

theorem comm_pow_of_apply (E : Fin n → Fin n → A) (hE : Formalism.REAL.GlRel E) (a b : Fin n) (m : ℕ)
    (c e : Fin n) : E a b * (Matrix.of E ^ m) c e - (Matrix.of E ^ m) c e * E a b =
      (if b = c then (Matrix.of E ^ m) a e else 0) - (if e = a then (Matrix.of E ^ m) c b else 0) := by
  first
  | exact @_root_.GlobalTheory.PowEntryCommutator.target
  | exact _root_.GlobalTheory.PowEntryCommutator.target
  | (apply _root_.GlobalTheory.PowEntryCommutator.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowEntryCommutator.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowEntryCommutator.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowEntryCommutator.target ..)

end GelfandCentral

theorem commute_gelfA : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (k : ℕ) (a b : Fin n), E a b * gelfA E k = gelfA E k * E a b := by
  intro A _ _ n E hE k a b
  rw [← sub_eq_zero, gelfA_eq_sum_pow, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [comm_pow_of_apply E hE, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]

end GlobalTheory.SmoothForms
