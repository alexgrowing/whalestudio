import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CurvAndMarginClosed
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoincarePointwiseStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

theorem margins_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X), X.p0 = 0 → Nonempty X.Ψ → (∀ x, Xa.ps0 x = 0) → IsStrictDom X Xa.L → (∀ τ (a b : Fin r), a ≤ b → (Xa.Fp - kapW X - nd X • Xa.L) τ b ≤ (Xa.Fp - kapW X - nd X • Xa.L) τ a) → Margins X Xa := by
  intro E _ _ _ r X Xa h0 _ hps _ hgap
  have hA : ∀ (m : ℝ) x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ := fun m x0 ho z hz ξ => by
    rw [← IW.leviM_comb X x0 ho hz]
    exact (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ m
      (fun τ i j a _ => hgap τ i j a) (fun τ i j _ b => hgap τ i j b)
      (fun τ i j a _ => absurd a (by omega)) x0 ho z hz ξ
  have hB : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ leviO X x0 (phla X Xa.L) z ξ := fun x0 ho z hz ξ => by
    by_cases hξ : ξ = 0
    · subst hξ; simp [leviO, leviM, leviV]
    · exact (Xa.posL x0 (IW.orth_mem_dom X x0 ho) z hz ξ hξ).le
  have hP : ∀ x0 z ξ, leviO X x0 Xa.ps0 z ξ = 0 := fun x0 z ξ => by
    simp only [leviO, leviM, hps]
    rw [RgC.leviV_const, Complex.zero_re]
  refine ⟨⟨_, _, lt_add_one _, lt_add_one _, fun t _ x0 ho z hz ξ => ?_⟩,
    ⟨_, _, lt_add_one _, lt_add_one _, fun x0 ho z hz ξ => ?_⟩, hB, ⟨0, fun x _ => (hps x).le⟩,
    fun k P hP => ⟨hP, fun ξ hξ =>
      (GlobalTheory.PoincareSeriesCompare.not_isIso_of_definite X (Or.inl h0) ξ hξ).elim⟩⟩
  · rw [hP, mul_zero, add_zero]
    exact hA _ x0 ho z hz ξ
  · exact (hA _ x0 ho z hz ξ).trans
      (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (hB x0 ho z hz ξ)))

end GlobalTheory.Shares
