import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory

theorem X_sub_X_dvd_sub_aeval_update_variable {σ : Type} [DecidableEq σ] (a b : σ) (P : MvPolynomial σ ℝ) :
    (X b - X a : MvPolynomial σ ℝ) ∣ P - aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [aeval_C]
  | add p q hp hq =>
    have h := dvd_add hp hq
    rw [map_add]
    convert h using 1
    ring
  | mul_X p c hp =>
    rw [map_mul, aeval_X]
    have h2 : (X b - X a : MvPolynomial σ ℝ) ∣ X c - Function.update X b (X a) c := by
      by_cases h : c = b
      · subst h; simp
      · simp [Function.update_of_ne h]
    have e : p * X c - aeval (Function.update X b (X a)) p * Function.update X b (X a) c
        = (p - aeval (Function.update X b (X a)) p) * X c
          + aeval (Function.update X b (X a)) p * (X c - Function.update X b (X a) c) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right h2 _)

theorem swap_odd_dvd : ∀ {σ : Type} [DecidableEq σ] (a b : σ), a ≠ b → ∀ P : MvPolynomial σ ℝ,
    rename (Equiv.swap a b) P = -P → (X b - X a : MvPolynomial σ ℝ) ∣ P := by
  intro σ _ a b hab P hP
  have hcomp : (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) ∘ (Equiv.swap a b)
      = Function.update X b (X a) := by
    funext i
    simp only [Function.comp_apply]
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left, Function.update_self, Function.update_of_ne hab]
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right, Function.update_of_ne hab, Function.update_self]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
  have h1 : aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P = - aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P := by
    have := congrArg (aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a))) hP
    rw [aeval_rename, hcomp, map_neg] at this
    exact this
  have h0 : aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P = 0 := self_eq_neg.mp h1
  have := X_sub_X_dvd_sub_aeval_update_variable a b P
  rwa [h0, sub_zero] at this
end GlobalTheory
