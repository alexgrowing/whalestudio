import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfGenericPolarization
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
theorem _root_.GlobalTheory.T.isIso_of_generic_polarization : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (GG : PDivGroup p R) (φ : GG ⟶ GG.dual) (g : ℕ), GG.height = 2 * g → IsIso (PDivGroup.baseChangeMap K φ) → (∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra R k], g ≤ Module.finrank k (k ⊗[R] Cot R (GG.A 1))) → IsIso φ := by
  first | exact @GlobalTheory.PDivGroup.isIso_of_isIso_baseChange_of_cot | exact GlobalTheory.PDivGroup.isIso_of_isIso_baseChange_of_cot | (intros; apply GlobalTheory.PDivGroup.isIso_of_isIso_baseChange_of_cot <;> assumption)
