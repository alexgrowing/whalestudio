import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveEmbeddingMinimalPrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
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
theorem _root_.GlobalTheory.T.exists_injective_embedding_minimal_prime : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K] (D : Type) [CommRing D] [Algebra R D] [Module.Flat R D] [Algebra.IsAlgebraic R D] (P : Ideal D), P ∈ minimalPrimes D → ∃ em : D ⧸ P →ₐ[R] K, Function.Injective em := by
  first | exact @GlobalTheory.Div.exists_algHom_quotient_minimalPrime_injective | exact GlobalTheory.Div.exists_algHom_quotient_minimalPrime_injective | (intros; apply GlobalTheory.Div.exists_algHom_quotient_minimalPrime_injective <;> assumption)
