import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOfLocalPrime
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
theorem _root_.GlobalTheory.T.exists_global_of_local_prime : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (A : Type) [CommRing A] [Algebra R A] [Finite (A →ₐ[R] K)] (r : A) (f : (A →ₐ[R] K) → K), (∀ (P : Ideal A) [P.IsPrime], r ∉ P → ∃ c : Localization.AtPrime P, ∀ ψ : Localization.AtPrime P →ₐ[R] K, ψ c = f (ψ.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime P)))) → ∃ (k : ℕ) (a : A), ∀ ψ : A →ₐ[R] K, ψ a = ψ r ^ k * f ψ := by
  first | exact @GlobalTheory.AlgPointsLocal.exists_pow_mul_of_locally_integral | exact GlobalTheory.AlgPointsLocal.exists_pow_mul_of_locally_integral | (intros; apply GlobalTheory.AlgPointsLocal.exists_pow_mul_of_locally_integral <;> assumption)
