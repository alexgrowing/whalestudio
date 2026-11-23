import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairingFunctorial
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
theorem _root_.GlobalTheory.T.torsion_pairing_functorial : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N N' : ℕ), N ≠ 0 → N' ≠ 0 → ∀ σ : ∀ (B : Type) [CommRing B] [Algebra R B], Tors G N B → Tors G N' B → B, (∀ (B C : Type) [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) (x : Tors G N B) (y : Tors G N' B), σ C (torsMap φ x) (torsMap φ y) = φ (σ B x y)) → (∀ x y, σ K x y = 0) → ∀ (B : Type) [CommRing B] [Algebra R B] (x : Tors G N B) (y : Tors G N' B), σ B x y = 0 := by
  first | exact @GlobalTheory.GroupBplus.Aff.natFn_pair_eq_zero | exact GlobalTheory.GroupBplus.Aff.natFn_pair_eq_zero | (intros; apply GlobalTheory.GroupBplus.Aff.natFn_pair_eq_zero <;> assumption)
