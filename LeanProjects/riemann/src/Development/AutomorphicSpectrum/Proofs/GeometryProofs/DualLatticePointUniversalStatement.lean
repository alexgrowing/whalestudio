import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticePointUniversal
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_point_universal : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), ∃ u : ob x (Module.Dual R L) ⟶ G, zsec x ≫ u = 1 ∧ (∀ e : L, hom x (Module.Dual.eval R L e) ≫ u = M.pt e) ∧ ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (v : ob x V ⟶ G), zsec x ≫ v = 1 → ∃! φ : Module.Dual R L →ₗ[R] V, hom x φ ≫ u = v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tan.Univ.tangent_universal | exact GlobalTheory.CompanionTheory.Ar.BT.Tan.Univ.tangent_universal | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tan.Univ.tangent_universal <;> assumption)
