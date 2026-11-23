import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LinearIndependentCoordinatesDenominator
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_independent_coordinates_denominator : ∀ (L : Type) [Field L] [NumberField L] (M : Type) [AddCommGroup M] [Module (𝓞 L) M] [Module.Finite (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M] (i : ℕ) (f : Fin i → M), LinearIndependent (𝓞 L) f → i = Module.finrank (𝓞 L) M → ∃ c : M →ₗ[𝓞 L] (Fin i → L), Function.Injective c ∧ (∀ j, c (f j) = Pi.single j 1) ∧ ∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧ ∀ j, (D : L) * c x j = a j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent | exact GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent <;> assumption)
