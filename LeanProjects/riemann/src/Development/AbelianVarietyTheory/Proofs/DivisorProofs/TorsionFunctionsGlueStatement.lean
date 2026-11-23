import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFunctionsGlue
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
theorem _root_.GlobalTheory.T.torsion_functions_glue : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (Idx : Type) (q : Idx → PrimeSpectrum R) (c : ∀ i, PreChart G N (q i)), (∀ (k : Type) [Field k] [Algebra R k] (z : Tors G N k), ∃ i, Set.range z.1.left ⊆ (c i).W) → ∀ g : Tors G N K → K, (∀ i, ∃ a : (c i).C, ∀ ψ : (c i).C →ₐ[R] K, ψ a = g (torsMap ψ (c i).j)) → ∃ σ, IsNatFn G N σ ∧ ∀ x, σ K x = g x := by
  first | exact @GlobalTheory.GroupBplus.Aff.Glue.exists_isNatFn_of_charts | exact GlobalTheory.GroupBplus.Aff.Glue.exists_isNatFn_of_charts | (intros; apply GlobalTheory.GroupBplus.Aff.Glue.exists_isNatFn_of_charts <;> assumption)
