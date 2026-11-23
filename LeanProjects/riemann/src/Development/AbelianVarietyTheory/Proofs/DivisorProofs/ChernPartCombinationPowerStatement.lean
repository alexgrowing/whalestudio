import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPower
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarComplexPointsCompactStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_part_combination_power : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (ε : ℤˣ),
    ((comb L n).φ σ).chernPart D ε = (hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε := by
  first | exact @GlobalTheory.ChernTop.chernPart_comb_eq_part | exact GlobalTheory.ChernTop.chernPart_comb_eq_part | (intros; apply GlobalTheory.ChernTop.chernPart_comb_eq_part <;> assumption)
