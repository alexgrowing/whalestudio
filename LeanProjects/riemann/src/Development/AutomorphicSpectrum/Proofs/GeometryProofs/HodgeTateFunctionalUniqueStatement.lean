import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUnique
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_functional_unique_mod_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → (N : R) ≠ 0 → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → (Γ.IsHT i M N χ w' ↔ ∃ u : Module.Dual R L, w' = w + N • u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.HT.isHT_iff | exact GlobalTheory.CompanionTheory.Ar.BT.HT.isHT_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.HT.isHT_iff <;> assumption)
