import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNeg
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_degree_neg : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K), IsBun C L → Function.Bijective B → IsBun C (dualLat C L B) ∧ deg C (dualLat C L B) = - deg C L ∧ dualLat C (dualLat C L B) B.flip = L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual | exact GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual <;> assumption)
