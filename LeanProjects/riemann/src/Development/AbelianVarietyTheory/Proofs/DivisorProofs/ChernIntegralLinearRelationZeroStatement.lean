import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralLinearRelationZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_linear_relation_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (D : ℕ) (J : Type) [Fintype J] (a : J → ℝ) (N : J → HermLB p), (∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, ∑ j, a j * c.chernDens ((N j).φ σ) y = 0) → ∀ (S : Set (CxPts p σ)) (g : CxPts p σ → ℝ), (∀ j, ((N j).φ σ).ChernIntegrableOn D S g) → ∑ j, a j * ((N j).φ σ).chernInt D S g = 0 := by
  first | exact @GlobalTheory.ChernLinRel.sum_chernInt_eq_zero | exact GlobalTheory.ChernLinRel.sum_chernInt_eq_zero | (intros; apply GlobalTheory.ChernLinRel.sum_chernInt_eq_zero <;> assumption)
