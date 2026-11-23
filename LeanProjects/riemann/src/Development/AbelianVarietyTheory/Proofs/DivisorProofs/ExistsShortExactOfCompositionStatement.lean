import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortExactOfComposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shortExact_of_composition : ∀ (X : Scheme.{0}) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact), f ≫ g = u → ∃ (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0), (ShortComplex.mk l m w₃).ShortExact ∧ q₀ ≫ l = g ≫ q₂ ∧ q₂ ≫ m = q₁ := by
  first | exact @GlobalTheory.ThirdIso.modules | exact GlobalTheory.ThirdIso.modules | (intros; apply GlobalTheory.ThirdIso.modules <;> assumption)
