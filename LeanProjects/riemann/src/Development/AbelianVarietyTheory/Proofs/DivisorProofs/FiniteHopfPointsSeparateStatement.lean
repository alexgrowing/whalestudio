import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparate
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
theorem _root_.GlobalTheory.T.finite_hopf_points_separate : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A], Finite (A →ₐ[R] K) ∧ (∀ a : A, (∀ ψ : A →ₐ[R] K, ψ a = 0) → a = 0) ∧ ∀ q : PrimeSpectrum R, Module.rankAtStalk (R := R) A q = Nat.card (A →ₐ[R] K) := by
  first | exact @GlobalTheory.HopfPoints.finite_points_separate_rank | exact GlobalTheory.HopfPoints.finite_points_separate_rank | (intros; apply GlobalTheory.HopfPoints.finite_points_separate_rank <;> assumption)
