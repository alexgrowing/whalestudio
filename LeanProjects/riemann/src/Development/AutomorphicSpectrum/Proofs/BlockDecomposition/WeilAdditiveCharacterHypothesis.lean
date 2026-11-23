import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WeilPsi

theorem choose_congr {α : Type*} {p q : α → Prop} (hpq : p = q) (hp : ∃ a, p a) (hq : ∃ a, q a) :
    hp.choose = hq.choose := by
  subst hpq
  rfl

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem unipotent_mul_val_real (x : F) (g : GL (Fin 2) F) :
    (uni2 x * g).val =
      !![g.val 0 0 + x * g.val 1 0, g.val 0 1 + x * g.val 1 1; g.val 1 0, g.val 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_left_unipotent_mul (x : F) (g : GL (Fin 2) F) : ((uni2 x * g).val).det = (g.val).det := by
  rw [unipotent_mul_val_real, Matrix.det_fin_two_of, Matrix.det_fin_two g.val]
  ring

theorem rW_shift (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b c d x : F)
    (hc0 : c = 0 → a * d = 1) (Φ : E → ℂ) :
    rW χ σ μE lam (a + x * c) (b + x * d) c d Φ 1 = (χ x : ℂ) * rW χ σ μE lam a b c d Φ 1 := by
  by_cases hc : c = 0
  · have had := hc0 hc
    subst hc
    have h1 : a * (b + x * d) * Algebra.norm F (1 : E) = x + a * b * Algebra.norm F (1 : E) := by
      rw [map_one]
      linear_combination x * had
    simp only [rW, if_true, mul_zero, add_zero]
    rw [h1, AddChar.map_add_eq_mul]
    push_cast
    ring
  · have hk : ∀ u : E,
        ((χ (((a + x * c) * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c) : Circle) : ℂ) * Φ u =
          (χ x : ℂ) * (((χ ((a * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c) : Circle) : ℂ) * Φ u) := by
      intro u
      have h2 : ((a + x * c) * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c =
          x + (a * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c := by
        rw [map_one]
        field_simp
        ring
      rw [h2, AddChar.map_add_eq_mul]
      push_cast
      ring
    simp only [rW, if_neg hc, hk]
    rw [integral_const_mul]
    ring

theorem weil_whittaker_unipotent_equivariance (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ)
    (Φ : E → ℂ) (x : F) (g : GL (Fin 2) F) :
    Wc χ σ μE lam c Φ (uni2 x * g) = (χ x : ℂ) * Wc χ σ μE lam c Φ g := by
  have hdet := det_left_unipotent_mul x g
  have hΔ : (g.val).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g.val).1 g.isUnit).ne_zero
  unfold Wc
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · have h' : ∃ t : Eˣ, Algebra.norm F (t : E) = ((uni2 x * g).val).det := by rwa [hdet]
    rw [dif_pos h', dif_pos h]
    have hch : h'.choose = h.choose :=
      choose_congr (by simp only [hdet]) h' h
    have e00 : (uni2 x * g).val 0 0 = g.val 0 0 + x * g.val 1 0 := by
      rw [unipotent_mul_val_real]; simp
    have e01 : (uni2 x * g).val 0 1 = g.val 0 1 + x * g.val 1 1 := by
      rw [unipotent_mul_val_real]; simp
    have e10 : (uni2 x * g).val 1 0 = g.val 1 0 := by
      rw [unipotent_mul_val_real]; simp
    have e11 : (uni2 x * g).val 1 1 = g.val 1 1 := by
      rw [unipotent_mul_val_real]; simp
    have hsplit : (g.val 0 0 + x * g.val 1 0) / (g.val).det =
        g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det) := by
      ring
    have hc0 : g.val 1 0 / (g.val).det = 0 → g.val 0 0 / (g.val).det * g.val 1 1 = 1 := by
      intro h0
      have hC : g.val 1 0 = 0 := by
        rcases div_eq_zero_iff.1 h0 with h1 | h1
        · exact h1
        · exact absurd h1 hΔ
      have hD : (g.val).det = g.val 0 0 * g.val 1 1 := by
        rw [Matrix.det_fin_two g.val, hC]
        ring
      rw [div_mul_eq_mul_div, ← hD]
      exact div_self hΔ
    rw [hch, hdet, e00, e01, e10, e11, hsplit,
      rW_shift χ σ μE lam _ _ _ _ x hc0]
    ring
  · have h' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((uni2 x * g).val).det := by rwa [hdet]
    rw [dif_neg h', dif_neg h, mul_zero]

end

theorem wPsi : Ad3.K.GL2LocalData.WPsi := by
  unfold Ad3.K.GL2LocalData.WPsi Ad3.K.GL2LocalData.ForEF
  intro F _ _ _ _ _ _ _ χ _ _ E _ _ _ _ _ _ _ _ _ σ _ η _ c Φ x g
  exact weil_whittaker_unipotent_equivariance χ σ _ _ c Φ x g

end GlobalTheory.CompanionTheory.WeilPsi
