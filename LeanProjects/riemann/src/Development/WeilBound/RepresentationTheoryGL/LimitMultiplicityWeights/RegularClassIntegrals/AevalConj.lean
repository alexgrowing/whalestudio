import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
import Mathlib.LinearAlgebra.Lagrange
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideTer

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix Polynomial
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PLagr

variable {n : ℕ}

lemma cd_mul {F G : Mx n → Matrix (Fin n) (Fin n) ℂ} (hF : ∀ a b, ContDiff ℝ ∞ (fun Y => F Y a b))
    (hG : ∀ a b, ContDiff ℝ ∞ (fun Y => G Y a b)) : ∀ a b, ContDiff ℝ ∞ (fun Y => (F Y * G Y) a b) := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun j _ => (hF a j).mul (hG j b)

lemma cd_pow (k : ℕ) : ∀ a b, ContDiff ℝ ∞ (fun Y : Mx n => ((Matrix.of Y) ^ k) a b) := by
  induction k with
  | zero => intro a b; simp only [pow_zero]; exact contDiff_const
  | succ k ih =>
    simp only [pow_succ]
    exact cd_mul ih (fun a b => by simp only [Matrix.of_apply]; exact contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) a b)

lemma cd_aeval (P : ℂ[X]) : ∀ a b, ContDiff ℝ ∞ (fun Y : Mx n => (aeval (Matrix.of Y) P) a b) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => intro a b; simp only [map_add, Matrix.add_apply]; exact (hp a b).add (hq a b)
  | monomial k c =>
    simp only [Polynomial.aeval_monomial]
    exact cd_mul (fun a b => contDiff_const) (cd_pow k)

lemma conj_pow (g g' D : Matrix (Fin n) (Fin n) ℂ) (h1 : g' * g = 1) (h2 : g * g' = 1) (k : ℕ) :
    (g' * D * g) ^ k = g' * D ^ k * g :=
  _root_.UpperTheory.Reformulated.B.Yhd8.main g g' D h1 h2 k

lemma aeval_conj (g g' D : Matrix (Fin n) (Fin n) ℂ) (h1 : g' * g = 1) (h2 : g * g' = 1) (P : ℂ[X]) :
    aeval (g' * D * g) P = g' * aeval D P * g := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, add_mul]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, conj_pow g g' D h1 h2,
      ← Algebra.smul_def, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]

lemma aeval_diag (l : Fin n → ℂ) (P : ℂ[X]) :
    aeval (diagonal l) P = diagonal fun j => P.eval (l j) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, Matrix.diagonal_add]; simp [Polynomial.eval_add]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Matrix.diagonal_pow, Matrix.algebraMap_eq_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp [Polynomial.eval_monomial]

end PLagr

open PLagr in
theorem lagr : Lagr := by
  intro n l hl
  refine ⟨fun i Y => fun a b => (aeval (Matrix.of Y) (Lagrange.basis Finset.univ l i)) a b, fun i => ?_, ?_⟩
  · exact contDiff_pi.2 fun a => contDiff_pi.2 fun b => cd_aeval _ a b
  · intro i g g' h1 h2
    change aeval (g' * diagonal l * g) (Lagrange.basis Finset.univ l i) = _
    rw [aeval_conj g g' _ h1 h2, aeval_diag]
    have hv : (fun j => (Lagrange.basis Finset.univ l i).eval (l j)) = Pi.single i 1 := by
      funext j
      by_cases h : j = i
      · subst h
        rw [Pi.single_eq_same, Lagrange.eval_basis_self hl.injOn (Finset.mem_univ _)]
      · rw [Pi.single_eq_of_ne h, Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)]
    rw [hv, Matrix.diagonal_single]

end MainStatements.WeightKernel

end
