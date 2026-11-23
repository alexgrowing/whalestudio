import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo

open MvPowerSeries ReciprocityTheory.PGsh

namespace GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

private theorem jacobian_logFGL_lg_eq_one {d : ℕ} (G : LogFGL v d) :
    FormalSeries.jacobian G.lg = 1 := by
  ext i j
  rw [FormalSeries.jacobian_apply, G.lg_lin i j, Matrix.one_apply]

private theorem exists_subst_inverse_logFGL_lg {d : ℕ} (G : LogFGL v d) :
    ∃ w : Fin d → MvPowerSeries (Fin d) C, (∀ j, constantCoeff (w j) = 0) ∧
      (∀ i, subst w (G.lg i) = X i) ∧ ∀ j, subst G.lg (w j) = X j :=
  FormalSeries.exists_subst_inverse G.lg_const (B := 1)
    (by rw [jacobian_logFGL_lg_eq_one, Matrix.mul_one]) (by rw [jacobian_logFGL_lg_eq_one, Matrix.one_mul])

theorem isExp_expOf {d : ℕ} (G : LogFGL v d) : IsExp G (expOf G) := by
  obtain ⟨w, hw0, hw1, -⟩ := exists_subst_inverse_logFGL_lg G
  exact Classical.epsilon_spec (p := IsExp G) ⟨w, hw0, hw1⟩

theorem isExp_eq_of_subst_lg {d : ℕ} (G : LogFGL v d) {w : Fin d → MvPowerSeries (Fin d) C}
    (h2 : ∀ j, subst G.lg (w j) = X j) {e : Fin d → MvPowerSeries (Fin d) C} (he : IsExp G e) :
    e = w := by
  obtain ⟨he0, he1⟩ := he
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have hes : HasSubst e := hasSubst_of_constantCoeff_zero he0
  funext j
  calc e j = subst e (X j : MvPowerSeries (Fin d) C) := (subst_X hes j).symm
    _ = subst e (subst G.lg (w j)) := by rw [h2 j]
    _ = subst (fun s => subst e (G.lg s)) (w j) := subst_comp_subst_apply hlg hes (w j)
    _ = subst (X : Fin d → MvPowerSeries (Fin d) C) (w j) := by simp only [he1]
    _ = w j := by rw [subst_self]; rfl

theorem isExp_unique {d : ℕ} (G : LogFGL v d) {e : Fin d → MvPowerSeries (Fin d) C}
    (he : IsExp G e) : e = expOf G := by
  obtain ⟨w, -, -, hw2⟩ := exists_subst_inverse_logFGL_lg G
  rw [isExp_eq_of_subst_lg G hw2 he, isExp_eq_of_subst_lg G hw2 (isExp_expOf G)]

theorem subst_lg_expOf {d : ℕ} (G : LogFGL v d) (a : Fin d) :
    subst G.lg (expOf G a) = (X a : MvPowerSeries (Fin d) C) := by
  obtain ⟨w, -, -, hw2⟩ := exists_subst_inverse_logFGL_lg G
  rw [isExp_eq_of_subst_lg G hw2 (isExp_expOf G)]
  exact hw2 a

theorem expOf_spec {d : ℕ} (G : LogFGL v d) :
    IsExp G (expOf G) ∧ (∀ e, IsExp G e → e = expOf G) ∧
      ∀ a, subst G.lg (expOf G a) = (X a : MvPowerSeries (Fin d) C) :=
  ⟨isExp_expOf G, fun _ he => isExp_unique G he, subst_lg_expOf G⟩

end GlobalTheory.FGDepth
