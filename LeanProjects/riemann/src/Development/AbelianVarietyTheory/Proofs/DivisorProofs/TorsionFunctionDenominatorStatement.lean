import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFunctionDenominator
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
theorem _root_.GlobalTheory.T.torsion_function_denominator : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), c.IsGrp → ∀ f : Tors G N K → K, (∀ s : Tors G N K, ∃ a : c.C, ∀ ψ : c.C →ₐ[R] K, ψ a = f (s * torsMap ψ c.j)) → ∃ k : ℕ, c.r ^ k • f ∈ ord G N K := by
  first | exact @GlobalTheory.GroupBplus.Aff.pow_smul_mem_ord_of_chart | exact GlobalTheory.GroupBplus.Aff.pow_smul_mem_ord_of_chart | (intros; apply GlobalTheory.GroupBplus.Aff.pow_smul_mem_ord_of_chart <;> assumption)
