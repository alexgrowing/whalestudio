import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueTranslatedProductValuationBound
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_translated_product_valuation_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (N n' A Bn : ℕ) (α β : 𝓞 E), Odd N → (N : 𝓞 E) = β * α * n' → α * H.bar α = (A : 𝓞 E) → β * H.bar β = (Bn : 𝓞 E) → IsUnit (n' : T.V) → ∀ (x₁ x₂ : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ b, x₁ b ^ (N ^ 2) = 1 ∧ x₂ b ^ (N ^ 2) = 1 ∧ (x₁ b ≫ Xo.univ.t.act.act (α * β)) ^ (n' ^ 2) = 1 ∧ (x₂ b ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (x₁ b) (x₂ b) (F b)) → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ HH c w n → MvPolynomial.map io P ∈ FFV (Dw := Dw) T w n → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹) * hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) P) := by
  first | exact @GlobalTheory.PlaceInt.TermBound.term_bound | exact GlobalTheory.PlaceInt.TermBound.term_bound | (intros; apply GlobalTheory.PlaceInt.TermBound.term_bound <;> assumption)
