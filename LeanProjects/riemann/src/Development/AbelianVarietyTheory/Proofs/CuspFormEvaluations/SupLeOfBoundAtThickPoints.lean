import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem maj_complex_smul_normSq {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ)
    (v : Fin r → ℂ) : X.maj x τ (c • v) = ‖c‖ ^ 2 * X.maj x τ v := by
  have hl : ∀ u, hermC τ.1 X.Gm (c • v) u = c * hermC τ.1 X.Gm v u := by
    intro u
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hr : hermC τ.1 X.Gm v (c • v) = conj c * hermC τ.1 X.Gm v v := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hc : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 : X.posPart x τ (c • v) = ‖c‖ ^ 2 * X.posPart x τ v := by
    unfold Data.posPart
    rw [← Complex.re_ofReal_mul, ← hc]
    congr 1
    simp only [hl, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have h2 : (hermC τ.1 X.Gm (c • v) (c • v)).re = ‖c‖ ^ 2 * (hermC τ.1 X.Gm v v).re := by
    rw [hl, hr, ← mul_assoc, hc, Complex.re_ofReal_mul]
  unfold Data.maj
  rw [h1, h2]
  ring

end GlobalTheory
