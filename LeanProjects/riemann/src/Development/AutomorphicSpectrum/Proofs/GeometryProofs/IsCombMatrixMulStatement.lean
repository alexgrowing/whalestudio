import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombMatrixMul
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_comb_matrix_mul : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (m n k : ℕ) (v : Fin n → (epsAt x ⟶ G)) (u : Fin m → (epsAt x ⟶ G)) (w : Fin k → (epsAt x ⟶ G)) (A : Matrix (Fin k) (Fin m) F) (C : Matrix (Fin m) (Fin n) F), (∀ i, IsTanAt G x (v i)) → (∀ i, IsComb (C i) v (u i)) → (∀ i, IsComb (A i) u (w i)) → ∀ i, IsComb ((A * C) i) v (w i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul | exact GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul <;> assumption)
