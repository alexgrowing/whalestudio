import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenvectorLinearCombination
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_linear_combination : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G), (∀ i, IsEigVec act x σ (v i)) → IsComb cf v w → IsEigVec act x σ w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombEig.isEigVec_comb | exact GlobalTheory.CompanionTheory.Ar.CombEig.isEigVec_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.CombEig.isEigVec_comb <;> assumption)
