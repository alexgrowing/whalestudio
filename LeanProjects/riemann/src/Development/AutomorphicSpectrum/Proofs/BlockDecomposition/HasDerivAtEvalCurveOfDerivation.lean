import Mathlib

open MvPolynomial
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Polynomial

theorem hasDerivAt_eval_curve_of_derivation {σ : Type}
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (γ : ℝ → σ → ℂ) (s : ℝ)
    (hγ : ∀ v, HasDerivAt (fun u => γ u v) (MvPolynomial.eval (γ s) (D (MvPolynomial.X v))) s)
    (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun u => MvPolynomial.eval (γ u) P) (MvPolynomial.eval (γ s) (D P)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h0 : D (MvPolynomial.C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact D.map_algebraMap a
    simp only [MvPolynomial.eval_C, h0, map_zero]
    exact hasDerivAt_const s a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p v hp =>
    have e : MvPolynomial.eval (γ s) (D (p * MvPolynomial.X v)) =
        MvPolynomial.eval (γ s) (D p) * γ s v +
          MvPolynomial.eval (γ s) p * MvPolynomial.eval (γ s) (D (MvPolynomial.X v)) := by
      rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, MvPolynomial.eval_X]
      ring
    have hf : (fun u => MvPolynomial.eval (γ u) (p * MvPolynomial.X v)) =
        fun u => MvPolynomial.eval (γ u) p * γ u v := by
      funext u; simp
    rw [e, hf]
    exact hp.mul (hγ v)

end GlobalTheory.CompanionTheory.Polynomial
