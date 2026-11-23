import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem c1F_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L : HermLB p, c1F hX σ L.dual = -c1F hX σ L := by
  intro k _ X _ p D hX σ L
  funext x
  have e : (fun v => (L.dual.φ σ).φ (pick (L.dual.φ σ).isLB x.pt) (x.ch.symm v)) =
      fun v => -(L.φ σ).φ (pick (L.φ σ).isLB x.pt) (x.ch.symm v) := rfl
  have e₂ : ∀ (u : ReciprocityTheory.L2DbarEstimates.V D → ℝ) (z : ReciprocityTheory.L2DbarEstimates.V D),
      GlobalTheory.HermFrame.ddc (fun v => -u v) z = fun ξ η => -GlobalTheory.HermFrame.ddc u z ξ η := by
    intro u z
    funext ξ η
    simp only [GlobalTheory.HermFrame.ddc, GlobalTheory.leviForm_neg, neg_apply, mul_neg]
  simp only [c1F, Pi.neg_apply]
  rw [e, e₂, ofValues, ofValues]
  simp only [neg_smul, Finset.sum_neg_distrib]

end GlobalTheory.LineForm
