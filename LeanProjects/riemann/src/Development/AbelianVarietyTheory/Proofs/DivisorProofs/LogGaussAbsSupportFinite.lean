import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.GaussAbsMulOfMonomialOrder
import ReciprocityTheory.SemistableReduction.LogNormCoeffSubLeBlockSphereLogMean
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussAbsMulSupportFinite

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSFinPart

theorem log_gaussAbs_support_finite {E : Type} [Field E] [NumberField E] {σ : Type}
    (g : MvPolynomial σ E) :
    (Function.support fun v : FinitePlace E => Real.log (gaussAbs v g)).Finite :=
  ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_support_finite g

theorem finPart_props : ∀ (E : Type) [Field E] [NumberField E] (σ τ : Type),
    (∀ g : MvPolynomial σ E, g ≠ 0 → {v : FinitePlace E | gaussAbs v g ≠ 1}.Finite ∧
      ∀ v : FinitePlace E, 0 < gaussAbs v g) ∧
    (∀ (g : MvPolynomial σ E) (g' : MvPolynomial τ E), g ≠ 0 → g' ≠ 0 →
      (∀ v : FinitePlace E, gaussAbs v g' ≤ gaussAbs v g) → finPart g' ≤ finPart g) ∧
    ∀ (g : MvPolynomial σ E) (m : σ →₀ ℕ), coeff m g ≠ 0 →
      -mean E (fun s => Real.log ‖s (coeff m g)‖) ≤ finPart g := by
  intro E _ _ σ τ
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast Module.finrank_pos
  refine ⟨fun g hg => ⟨?_, fun v => gauss_abs_pos_of_ne_zero v g hg⟩, ?_, ?_⟩
  · exact ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_mulSupport_finite g hg
  · intro g g' hg hg' hle
    unfold finPart
    refine div_le_div_of_nonneg_right ?_ hd.le
    exact finsum_le_finsum' (log_gaussAbs_support_finite g') (log_gaussAbs_support_finite g)
      (fun v => Real.log_le_log (gauss_abs_pos_of_ne_zero v g' hg') (hle v))
  · intro g m hm
    have hg : g ≠ 0 := by
      rintro rfl; exact hm (by simp)
    set c := coeff m g with hc
    have h1 : ∑ᶠ v : FinitePlace E, Real.log (v c) ≤ ∑ᶠ v : FinitePlace E, Real.log (gaussAbs v g) :=
      finsum_le_finsum'
        ((FinitePlace.hasFiniteMulSupport hm).subset (by
          intro v hv h1; apply hv; simp only at h1 ⊢; rw [h1, Real.log_one]))
        (log_gaussAbs_support_finite g)
        (fun v => Real.log_le_log (FinitePlace.pos_iff.mpr hm) (coeff_le_gauss_abs v g m))
    rw [ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.finsum_log_norm c hm] at h1
    unfold mean finPart
    rw [sum_log_norm_embedding_eq c hm, ← neg_div]
    exact div_le_div_of_nonneg_right h1 hd.le

end GlobalTheory.HSFinPart
