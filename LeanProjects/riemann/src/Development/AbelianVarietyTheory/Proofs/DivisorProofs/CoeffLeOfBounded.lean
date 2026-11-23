import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGaussAbsSupportFinite

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSFloor

theorem coeff_le_of_bounded {E : Type} [Field E] {σ : Type} [Fintype σ] (k : MvPolynomial σ E)
    (s : E →+* ℂ) (B : ℝ) (hB : ∀ z : σ → ℂ, (∀ i, ‖z i‖ ≤ 1) → ‖eval₂ s z k‖ ≤ B) (m : σ →₀ ℕ) :
    ‖s (coeff m k)‖ ≤ B := by

  obtain ⟨θ, hθ⟩ := (ReciprocityTheory.MultiplicativeHeights.Closed.torus_l2_cauchy_inequality σ (MvPolynomial.map s k)).2 m
  have hz : ∀ i, ‖ReciprocityTheory.MultiplicativeHeights.torusPoint θ i‖ ≤ 1 := by
    intro i
    simp [ReciprocityTheory.MultiplicativeHeights.torusPoint, Complex.norm_exp]
  rw [MvPolynomial.coeff_map, MvPolynomial.eval_map] at hθ
  exact hθ.trans (hB _ hz)

theorem floor : ∀ (E : Type) [Field E] [NumberField E] (σ : Type) [Fintype σ] (k : MvPolynomial σ E)
    (B : (E →+* ℂ) → ℝ), k ≠ 0 →
    (∀ (s : E →+* ℂ) (z : σ → ℂ), (∀ i, ‖z i‖ ≤ 1) → ‖eval₂ s z k‖ ≤ B s) →
    -mean E (fun s => Real.log (B s)) ≤ finPart k := by
  intro E _ _ σ _ k B hk hB
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hk
  refine le_trans ?_ ((GlobalTheory.HSFinPart.finPart_props E σ σ).2.2 k m hm)
  rw [neg_le_neg_iff]
  unfold mean
  gcongr with τ _

  have hpos : 0 < ‖τ (coeff m k)‖ := norm_pos_iff.mpr ((map_ne_zero τ).mpr hm)
  exact Real.log_le_log hpos (coeff_le_of_bounded k τ (B τ) (hB τ) m)

end GlobalTheory.HSFloor
