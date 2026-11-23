import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateExtensionSurjectivePoints
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
theorem _root_.GlobalTheory.T.tate_extension_surjective_points : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (GG : PDivGroup p R) (GG₀ : PDivGroup p K) (e : GG₀ ≅ GG.baseChange K) (L : Type) [AddCommGroup L] (τ₀ : L →+ GG₀.Tate) (τ : L →+ GG.Tate), (∀ x, tateMap _ _ K e.hom (τ₀ x) = bcTate K (τ x)) → (∀ (n : ℕ) (φ : GG₀.A n →ₐ[K] K), ∃ x, tatePt (τ₀ x) n K = φ) → ∀ (n : ℕ) (k : Type) [Field k] [Algebra R k], (p : k) ≠ 0 → ∀ φ : GG.A n →ₐ[R] k, ∃ x, tatePt (τ x) n k = φ := by
  first | exact @GlobalTheory.tatePt_surjective_of_generic | exact GlobalTheory.tatePt_surjective_of_generic | (intros; apply GlobalTheory.tatePt_surjective_of_generic <;> assumption)
