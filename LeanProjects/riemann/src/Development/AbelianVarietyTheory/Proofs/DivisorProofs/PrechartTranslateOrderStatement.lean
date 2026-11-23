import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrechartTranslateOrder
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
theorem _root_.GlobalTheory.T.prechart_translate_order : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), c.IsGrp → ∀ (s₀ : Tors G N K) (u : c.C), ∃ (k : ℕ) (g : Tors G N K → K), g ∈ ord G N K ∧ (∀ ψ : c.C →ₐ[R] K, g (s₀ * torsMap ψ c.j) = algebraMap R K c.r ^ k * ψ u) ∧ ∀ x, (∀ ψ : c.C →ₐ[R] K, x ≠ s₀ * torsMap ψ c.j) → g x = 0 := by
  first | exact @GlobalTheory.GroupBplus.Aff.exists_extend_zero_mem_ord | exact GlobalTheory.GroupBplus.Aff.exists_extend_zero_mem_ord | (intros; apply GlobalTheory.GroupBplus.Aff.exists_extend_zero_mem_ord <;> assumption)
