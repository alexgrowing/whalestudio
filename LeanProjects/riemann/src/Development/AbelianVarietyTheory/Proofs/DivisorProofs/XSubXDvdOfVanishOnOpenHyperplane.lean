import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory

theorem mvPolynomial_eq_zero_of_vanish_on_open {σ : Type} [Fintype σ] (Q : MvPolynomial σ ℝ)
    (V : Set (σ → ℝ)) (hV : IsOpen V) (hne : V.Nonempty) (h : ∀ x ∈ V, eval x Q = 0) : Q = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.1 hV x hx
  refine MvPolynomial.funext_set u (fun i => ?_) (fun y hy => ?_)
  · exact infinite_of_mem_nhds (x i) ((hu i).1.mem_nhds (hu i).2)
  · rw [map_zero]
    exact h y (hsub hy)

theorem X_sub_X_dvd_of_vanish_on_open_hyperplane (σ : Type) [Fintype σ] [DecidableEq σ] (a b : σ)
    (P : MvPolynomial σ ℝ) (U : Set (σ → ℝ)) (hab : a ≠ b) (hU : IsOpen U)
    (hne : ∃ x ∈ U, x a = x b) (h : ∀ x ∈ U, x a = x b → eval x P = 0) :
    (X a - X b : MvPolynomial σ ℝ) ∣ P := by
  let s : σ → MvPolynomial σ ℝ := fun i => if i = a then X b else X i
  have hdvd : ∀ Q : MvPolynomial σ ℝ, (X a - X b : MvPolynomial σ ℝ) ∣ Q - bind₁ s Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq =>
      rw [map_add, add_sub_add_comm]
      exact dvd_add hp hq
    | mul_X p i hp =>
      rw [map_mul, bind₁_X_right]
      have hi : (X a - X b : MvPolynomial σ ℝ) ∣ X i - s i := by
        by_cases hia : i = a
        · subst hia; simp [s]
        · simp [s, hia]
      have : p * X i - bind₁ s p * s i = (p - bind₁ s p) * X i + bind₁ s p * (X i - s i) := by
        ring
      rw [this]
      exact dvd_add (hp.mul_right _) (hi.mul_left _)
  have hev : ∀ x : σ → ℝ, eval x (bind₁ s P) = eval (Function.update x a (x b)) P := by
    intro x
    have h1 : eval x (bind₁ s P) = eval (fun i => eval x (s i)) P := eval₂Hom_bind₁ _ _ _ _
    rw [h1]
    congr 2
    funext i
    by_cases hia : i = a
    · subst hia; simp [s]
    · simp [s, hia]
  have hzero : bind₁ s P = 0 := by
    have hc : Continuous (fun x : σ → ℝ => Function.update x a (x b)) :=
      continuous_id.update a (continuous_apply b)
    refine mvPolynomial_eq_zero_of_vanish_on_open _ _ (hU.preimage hc) ?_ ?_
    · obtain ⟨x, hx, hxab⟩ := hne
      refine ⟨x, ?_⟩
      simp only [Set.mem_preimage]
      rw [← hxab, Function.update_eq_self]
      exact hx
    · intro x hx
      rw [hev]
      refine h _ hx ?_
      simp [Function.update_of_ne hab.symm]
  simpa [hzero] using hdvd P

end GlobalTheory
