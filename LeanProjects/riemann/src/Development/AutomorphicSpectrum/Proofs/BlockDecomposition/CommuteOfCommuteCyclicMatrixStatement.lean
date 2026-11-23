import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteOfCommuteCyclicMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_of_commute_cyclic_matrix : ∀ (K : Type) [Field K] (R : Type) [CommRing R] [Algebra K R] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K), (∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v) → ∀ X Y : Matrix (Fin n) (Fin n) R, X * γ.map (algebraMap K R) = γ.map (algebraMap K R) * X → Y * γ.map (algebraMap K R) = γ.map (algebraMap K R) * Y → X * Y = Y * X := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.commute_of_commute_cyclic | exact GlobalTheory.CompanionTheory.TorusCh.commute_of_commute_cyclic | (intros; apply GlobalTheory.CompanionTheory.TorusCh.commute_of_commute_cyclic <;> assumption)
