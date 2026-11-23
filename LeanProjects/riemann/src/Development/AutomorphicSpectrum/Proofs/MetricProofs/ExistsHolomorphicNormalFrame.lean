import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem xiPot_logSin_change_of_frame : ∀ (G g : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → IsUnit g.det → (gᴴ * G * g).PosDef ∧ (∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → xiPot (gᴴ * G * g) a = xiPot G ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) - 2 * Real.log ‖g 0 0 + g 0 1 * a‖ + Real.log ‖g.det‖) ∧ ∀ a₀ a₁ : ℂ, g 0 0 + g 0 1 * a₀ ≠ 0 → g 0 0 + g 0 1 * a₁ ≠ 0 → logSin (gᴴ * G * g) a₀ a₁ = logSin G ((g 1 0 + g 1 1 * a₀) / (g 0 0 + g 0 1 * a₀)) ((g 1 0 + g 1 1 * a₁) / (g 0 0 + g 0 1 * a₁)) := by
  intro G g hG hg
  have herm2_conj_lemma : ∀ (u w : Fin 2 → ℂ), herm2 (gᴴ * G * g) u w = herm2 G (g *ᵥ u) (g *ᵥ w) := by
    intro u w
    unfold herm2
    rw [← Matrix.mulVec_mulVec w (gᴴ * G) g, ← Matrix.mulVec_mulVec (g *ᵥ w) gᴴ G,
      Matrix.dotProduct_mulVec (star u) gᴴ, Matrix.star_mulVec g u]
  have herm2_smul_lemma_2 : ∀ (s t : ℂ) (u w : Fin 2 → ℂ),
      herm2 G (s • u) (t • w) = star s * t * herm2 G u w := by
    intro s t u w
    have hsu : star (s • u) = star s • star u := by
      ext i
      simp [star_mul']
    unfold herm2
    rw [Matrix.mulVec_smul, hsu, dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  have ratio_lemma_3 : ∀ (x y p q r : ℝ), x ≠ 0 → y ≠ 0 →
      (x * y * r) ^ 2 / (x ^ 2 * p * (y ^ 2 * q)) = r ^ 2 / (p * q) := by
    intro x y p q r hx hy
    rw [show (x * y * r) ^ 2 = r ^ 2 * (x ^ 2 * y ^ 2) by ring,
      show x ^ 2 * p * (y ^ 2 * q) = (p * q) * (x ^ 2 * y ^ 2) by ring]
    exact mul_div_mul_right _ _ (mul_ne_zero (pow_ne_zero 2 hx) (pow_ne_zero 2 hy))
  have hdet : g.det ≠ 0 := hg.ne_zero
  have hv : ∀ b : ℂ, (![1, b] : Fin 2 → ℂ) ≠ 0 := by
    intro b h
    have h0 := congrFun h 0
    simp at h0
  have hre : ∀ b : ℂ, 0 < (herm2 G ![1, b] ![1, b]).re := fun b =>
    (Complex.pos_iff.1 (hG.dotProduct_mulVec_pos (hv b))).1
  have hdG : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  have hcc : ∀ c : ℂ, star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    intro c
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  have hre_mul : ∀ c z : ℂ, (star c * c * z).re = ‖c‖ ^ 2 * z.re := by
    intro c z
    rw [hcc, Complex.re_ofReal_mul]
  have hc : ∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → g *ᵥ ![1, a] =
      (g 0 0 + g 0 1 * a) • ![1, (g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)] := by
    intro a ha
    have ha' : g 0 0 + a * g 0 1 ≠ 0 := by rwa [mul_comm a]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
  refine ⟨hG.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det g).mpr hg)), ?_, ?_⟩
  · intro a ha
    unfold xiPot
    rw [herm2_conj_lemma, hc a ha, herm2_smul_lemma_2, hre_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_conjTranspose,
      show star g.det * G.det * g.det = star g.det * g.det * G.det by ring, hre_mul,
      Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)) (hre _).ne',
      Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr hdet)) hdG.ne', Real.log_pow, Real.log_pow]
    push_cast
    ring
  · intro a₀ a₁ h₀ h₁
    unfold logSin
    rw [herm2_conj_lemma, herm2_conj_lemma, herm2_conj_lemma, hc a₀ h₀, hc a₁ h₁, herm2_smul_lemma_2,
      herm2_smul_lemma_2, herm2_smul_lemma_2, hre_mul, hre_mul, norm_mul, norm_mul, norm_star,
      ratio_lemma_3 _ _ _ _ _ (norm_ne_zero_iff.mpr h₀) (norm_ne_zero_iff.mpr h₁)]

end GlobalTheory.CompanionTheory.Ar.PB
