import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulP
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_lattice_degree_mul_p : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)), IsBun C L → IsBun C (frobLat C p L) ∧ deg C (frobLat C p L) = p * deg C L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat | exact GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat <;> assumption)
