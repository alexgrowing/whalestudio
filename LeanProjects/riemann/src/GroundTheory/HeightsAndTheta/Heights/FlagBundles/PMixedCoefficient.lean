import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial

theorem MixedCoefficient.proof : MixedCoefficient.Statement := by
  intro S _ G A₁ A₂ v₁ v₂ h₁ h₂
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add] at hp hq ⊢
    rw [hp, hq]; ring
  | mul_X p i hp =>
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Derivation.leibniz, pderiv_X_self, smul_eq_mul,
        map_add, map_mul, eval_X, Matrix.cons_val_zero, mul_one] at hp ⊢
      have e : pderiv (1 : Fin 2) (X (0 : Fin 2) : MvPolynomial (Fin 2) S) = 0 :=
        pderiv_X_of_ne (by decide)
      rw [e]
      simp only [map_zero, mul_zero, zero_add]
      rw [hp]
      linear_combination (eval ![A₁, A₂] (pderiv 0 p) - v₂ * eval ![A₁, A₂] (pderiv 0 (pderiv 1 p))) * h₁
    · simp only [Fin.mk_one, Fin.isValue, Derivation.leibniz, pderiv_X_self, smul_eq_mul,
        map_add, map_mul, eval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one] at hp ⊢
      have e : pderiv (0 : Fin 2) (X (1 : Fin 2) : MvPolynomial (Fin 2) S) = 0 :=
        pderiv_X_of_ne (by decide)
      rw [e]
      simp only [map_zero, mul_zero, zero_add, add_zero]
      rw [hp]
      linear_combination (eval ![A₁, A₂] (pderiv 1 p) - v₁ * eval ![A₁, A₂] (pderiv 0 (pderiv 1 p))) * h₂

end GroundTheory.Heights₂.Heights.FlagBundles
