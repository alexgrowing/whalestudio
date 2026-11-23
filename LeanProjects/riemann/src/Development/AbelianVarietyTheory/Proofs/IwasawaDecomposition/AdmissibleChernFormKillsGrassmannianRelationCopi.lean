import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RenVar
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GrassTop

theorem ren_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) :
    ren τ (rel k) = GlobalTheory.PointChern.relPoly τ k := by
  simp [ren, rel, GlobalTheory.PointChern.relPoly, map_sum, renVar]

theorem admissibleChernForm_kills_grassmannianRelationCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), GlobalTheory.Schubert.admitted H Dw Θ →
    ∀ (τ : GlobalTheory.AllWt.Psi H) (j : MvPolynomial (Bool × ℕ) ℝ), j ∈ GlobalTheory.GrassTop.J Dw.p Dw.q →
    ∀ r : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (r * GlobalTheory.GrassTop.ren τ j) = 0 := by
  intro E _ _ _ H Dw Θ hA τ j hj
  obtain ⟨h1, h2, h3, -⟩ := hA
  unfold J at hj
  induction hj using Submodule.span_induction with
  | mem x hx =>
    intro r
    rcases hx with ⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · rw [ren_rel, mul_comm]; exact h1 τ k hk r
    · rw [mul_comm]
      simp only [ren, map_sub, rename_X, map_one]
      exact h2 _ r
    · rw [mul_comm]
      simp only [ren, rename_X]
      have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
      exact h3 _ _ (by simp only [renVar, if_true]; omega) r
    · rw [mul_comm]
      simp only [ren, rename_X]
      have hm : Dw.mult (conjEmb τ.1) = Dw.q := GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)
      exact h3 _ _ (by simp only [renVar]; simp only [Bool.false_eq_true, if_false]; omega) r
  | zero => intro r; simp
  | add x y _ _ hx hy => intro r; rw [map_add, mul_add, map_add, hx, hy, add_zero]
  | smul a x _ hx => intro r; rw [smul_eq_mul, map_mul (ren τ) a x, ← mul_assoc]; exact hx _

end GlobalTheory.GrassTop
