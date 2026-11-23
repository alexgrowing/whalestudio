import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombIdentityMatrix
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_comb_identity_matrix : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)), (∀ i, IsTanAt G x (v i)) → ∀ i, IsComb ((1 : Matrix (Fin n) (Fin n) F) i) v (v i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row | exact GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row <;> assumption)
