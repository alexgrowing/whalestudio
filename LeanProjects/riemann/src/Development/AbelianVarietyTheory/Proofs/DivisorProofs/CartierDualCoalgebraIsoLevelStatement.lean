import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualCoalgebraIsoLevel
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
theorem _root_.GlobalTheory.T.cartier_dual_coalgebra_iso_level : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (θ : TorsPt G N A), IsLevel K θ → ∀ F : K ⊗[R] CartierDual R A →ₐc[K] K ⊗[R] A, (∀ (B : Type) [CommRing B] [Algebra R B] (z z' : Tors G N B), ∃ c : B, ∀ (ψ : B →ₐ[R] K) (s s' : A →ₐ[R] R), θ.pt K (torsMap ψ z) = (Algebra.ofId R K).comp s → θ.pt K (torsMap ψ z') = (Algebra.ofId R K).comp s' → ψ c = Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp s') (fun _ _ => .all _ _) (F ((1 : K) ⊗ₜ[R] (toConv s.toLinearMap : CartierDual R A)))) → ∀ l : CartierDual R A, ∃ a : A, F ((1 : K) ⊗ₜ[R] l) = (1 : K) ⊗ₜ[R] a := by
  first | exact @GlobalTheory.GroupBplus.Aff.bialgHom_dual_integral_of_pairs | exact GlobalTheory.GroupBplus.Aff.bialgHom_dual_integral_of_pairs | (intros; apply GlobalTheory.GroupBplus.Aff.bialgHom_dual_integral_of_pairs <;> assumption)
