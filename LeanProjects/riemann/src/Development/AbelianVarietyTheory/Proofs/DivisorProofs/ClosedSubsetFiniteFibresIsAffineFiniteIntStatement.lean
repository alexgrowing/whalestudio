import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetFiniteFibresIsAffineFiniteInt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedSubset_finiteFibres_isAffine_finite_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (T : Closeds X), (∀ ℓ : ℕ, ((T : Set X) ∩ fib X ℓ).Finite) → IsAffine (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧ Module.Finite ℤ Γ((Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) := by
  first | exact @GlobalTheory.HSAmp.closeds_finite_int | exact GlobalTheory.HSAmp.closeds_finite_int | (intros; apply GlobalTheory.HSAmp.closeds_finite_int <;> assumption)
