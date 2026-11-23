import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithResidueCharFibreStructure
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projArith_residueCharFibre_structure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∀ x : X, x ∈ fib X 0 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ x ∈ fib X ℓ) ∧ (∀ ℓ : ℕ, ℓ ≠ 0 → IsClosed (fib X ℓ)) ∧ (∀ x y : X, x ⤳ y → y ∈ fib X 0 → x ∈ fib X 0) ∧ (∀ ℓ : ℕ, topologicalKrullDim (fib X ℓ) ≤ D) ∧ ∀ W : Set X, IsClosed W → ∃ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) ∧ W ⊆ closure (W ∩ fib X 0) ∪ ⋃ ℓ ∈ S, fib X ℓ := by
  first | exact @GlobalTheory.IntFib.fib_structure | exact GlobalTheory.IntFib.fib_structure | (intros; apply GlobalTheory.IntFib.fib_structure <;> assumption)
