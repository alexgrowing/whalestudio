import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal

open Filter Topology

namespace GlobalTheory

theorem fderiv_eq_fderiv_zero_of_const_differences {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (G : (Fin g → ℂ) → ℂ) (p : Λ → ℂ)
    (hG : Differentiable ℂ G) (hp : ∀ (l : Λ) (w : Fin g → ℂ), G (w + l) = G w + p l)
    (v : Fin g → ℂ) : fderiv ℂ G v = fderiv ℂ G 0 := by
  have hd : Differentiable ℂ (fun w => G (w + v) - G w) :=
    (hG.comp (differentiable_id.add_const v)).sub hG
  have hc : ∀ w, G (w + v) - G w = G (0 + v) - G 0 := fun w =>
    entire_apply_eq_of_periodic_of_span_real hd hΛ (fun x l hl => by
      have h1 := hp ⟨l, hl⟩ (x + v)
      have h2 := hp ⟨l, hl⟩ x
      simp only at h1 h2
      show G (x + l + v) - G (x + l) = G (x + v) - G x
      rw [add_right_comm, h1, h2]
      ring) w 0
  have he : (fun w => G (w + v)) = fun w => G w + (G (0 + v) - G 0) := by
    funext w
    rw [← hc w]
    ring
  have h1 : fderiv ℂ (fun w => G (w + v)) 0 = fderiv ℂ G (0 + v) := fderiv_comp_add_right v
  rw [he, fderiv_add_const, zero_add v] at h1
  exact h1.symm

theorem fderiv_zero_eq_of_const_differences :
    ∀ {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)), Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (G : (Fin g → ℂ) → ℂ) (p : Λ → ℂ), Differentiable ℂ G →
        (∀ (l : Λ) (w : Fin g → ℂ), G (w + l) = G w + p l) →
        ∀ l : Λ, fderiv ℂ G 0 l = p l := by
  intro g Λ hΛ G p hG hp l
  have hk := fderiv_eq_fderiv_zero_of_const_differences Λ hΛ G p hG hp
  have hd : Differentiable ℂ (fun w => G w - fderiv ℂ G 0 w) :=
    hG.sub (fderiv ℂ G 0).differentiable
  have hz : ∀ w, fderiv ℂ (fun w => G w - fderiv ℂ G 0 w) w = 0 := fun w => by
    have := ((hG w).hasFDerivAt.sub (fderiv ℂ G 0).hasFDerivAt).fderiv
    rw [hk w, sub_self] at this
    exact this
  have h := is_const_of_fderiv_eq_zero hd hz (l : Fin g → ℂ) 0
  have h2 := hp l 0
  rw [zero_add] at h2
  simp only [map_zero, sub_zero] at h
  rw [h2] at h
  linear_combination -h

end GlobalTheory
