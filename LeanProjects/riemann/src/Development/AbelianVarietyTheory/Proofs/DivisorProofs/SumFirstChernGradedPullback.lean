import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPower
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LineForm

theorem c1F_grLB_sum_pullback_eq_pullback_sum : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    c1F hY σ (VMetric.grLB fl' 0 (H.pull π w)) + c1F hY σ (VMetric.grLB fl' 1 (H.pull π w)) = c1F hY σ ((VMetric.grLB fl 0 H).pull π w) + c1F hY σ ((VMetric.grLB fl 1 H).pull π w) := by
  intro k _ X _ p D _ σ Y p' D' hY π w E h H fl fl'
  have ht (L M : HermLB p') : c1F hY σ L + c1F hY σ M = c1F hY σ (L.tens M) := by
    funext ⟨⟨c, y⟩, hy⟩
    exact ((congrArg₂ (· + ·) (ChernTop.c1F_eq_matForm_hessL hY L hy) (ChernTop.c1F_eq_matForm_hessL hY M hy)).trans
      (map_add (ChernTop.matForm D') _ _).symm).trans
      ((congrArg (ChernTop.matForm D') (ChernTop.hessL_tens L M hy)).symm.trans (ChernTop.c1F_eq_matForm_hessL hY (L.tens M) hy).symm)
  have hi (L M : HermLB p') (e : L.Isometric M) : c1F hY σ L = c1F hY σ M := by
    funext ⟨⟨c, y⟩, hy⟩
    exact (ChernTop.c1F_eq_matForm_hessL hY L hy).trans ((congrArg (ChernTop.matForm D')
      (e.hess_eq c hy (mem_pick (M.φ σ).isLB y) (mem_pick (L.φ σ).isLB y)).symm).trans (ChernTop.c1F_eq_matForm_hessL hY M hy).symm)
  rw [ht, ht]
  refine hi _ _ ?_
  have e₁ := (GlobalTheory.VMetric.isometric_grLB_tens_grLB_det k Y p' _ _ (H.pull π w) fl').trans
    (VMetric.isometric_det_pull H π w)
  have e₂ := (GlobalTheory.VMetric.isometric_grLB_tens_grLB_det k X p E h H fl).pull π w
  have e₃ := HermLB.isometric_pull_tens (L := VMetric.grLB fl 0 H) (M := VMetric.grLB fl 1 H) π w
  exact (e₁.trans e₂.symm).trans e₃

end GlobalTheory.LineForm
