import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCartierDual
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_cartier_dual : ∀ (R : Type) [CommRing R] (D : Type) [CommRing D] [HopfAlgebra R D] [Module.Finite R D] (g : ℕ) (x : Fin g → Cot R D) (r c : R), (∀ w : Cot R D, r • w ∈ Submodule.span R (Set.range x)) → (∀ w : Cot R D, c • w = 0) → ∃ (k : ℕ) (Λ : D), (∀ d : D, d * Λ = algebraMap R D (Coalgebra.counit (R := R) d) * Λ) ∧ Coalgebra.counit (R := R) Λ = r ^ k * c ^ g := by
  first | exact @GlobalTheory.HopfFitt.exists_integral | exact GlobalTheory.HopfFitt.exists_integral | (intros; apply GlobalTheory.HopfFitt.exists_integral <;> assumption)
