import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingLevelStructureFiniteFlat
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
theorem _root_.GlobalTheory.T.weil_pairing_level_structure_finite_flat : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (θ : TorsPt G N A), IsLevel K θ → ∀ e : (A →ₐ[R] K) → (A →ₐ[R] K) → K, (∀ x y z w : A →ₐ[R] K, toConv z = toConv x * toConv y → e z w = e x w * e y w ∧ e w z = e w x * e w y) → (∀ x y, e x y ≠ 0) → (∀ (B : Type) [CommRing B] [Algebra R B] (z z' : Tors G N B), ∃ c : B, ∀ ψ : B →ₐ[R] K, ψ c = e (θ.pt K (torsMap ψ z)) (θ.pt K (torsMap ψ z'))) → ∃ T : A ⊗[R] A, ∀ x y : A →ₐ[R] K, Algebra.TensorProduct.lift x y (fun _ _ => .all _ _) T = e x y := by
  first | exact @GlobalTheory.GroupBplus.Aff.exists_tensor_of_bicharacter | exact GlobalTheory.GroupBplus.Aff.exists_tensor_of_bicharacter | (intros; apply GlobalTheory.GroupBplus.Aff.exists_tensor_of_bicharacter <;> assumption)
