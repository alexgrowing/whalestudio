import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPower
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LineForm

theorem c1F_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L M : HermLB p, c1F hX σ (L.tens M) = c1F hX σ L + c1F hX σ M := by
  intro k _ X _ p D hX σ L M
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  show c1F hX σ (L.tens M) ⟨(c, y), hy⟩ = c1F hX σ L ⟨(c, y), hy⟩ + c1F hX σ M ⟨(c, y), hy⟩
  rw [GlobalTheory.ChernTop.c1F_eq_matForm_hessL hX _ hy, GlobalTheory.ChernTop.c1F_eq_matForm_hessL hX _ hy, GlobalTheory.ChernTop.c1F_eq_matForm_hessL hX _ hy,
    GlobalTheory.ChernTop.hessL_tens L M hy, map_add]

end GlobalTheory.LineForm
