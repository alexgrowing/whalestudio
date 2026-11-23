import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleExtensionOfGeneric
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
theorem _root_.GlobalTheory.T.tate_module_extension_of_generic : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (GG : PDivGroup p R) (GG₀ : PDivGroup p K) (e : GG₀ ≅ GG.baseChange K) (L : Type) [AddCommGroup L] (ε₀ : (PDivGroup.mu p K).Tate) (τ₀ : L →+ GG₀.Tate), ∃ (ε : (PDivGroup.mu p R).Tate) (τ : L →+ GG.Tate), (∀ n, muRoot ε₀ n = algebraMap R K (muRoot ε n)) ∧ ∀ x, tateMap _ _ K e.hom (τ₀ x) = bcTate K (τ x) := by
  first | exact @GlobalTheory.FracDescend.descend_tate_and_mu | exact GlobalTheory.FracDescend.descend_tate_and_mu | (intros; apply GlobalTheory.FracDescend.descend_tate_and_mu <;> assumption)
