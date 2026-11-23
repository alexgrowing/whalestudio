import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeLengthMonoStrict
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_length_mono_strict : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (ι : Type) [Fintype ι] (L L' : Submodule R (ι → R)), L ≤ L' → ∀ x y : NNReal, x ≠ 0 → HasLen v R ((ι → R) ⧸ L) x → HasLen v R ((ι → R) ⧸ L') y → x ≤ y ∧ (x = y → L = L') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.submodule_eq_of_hasLen_eq | exact GlobalTheory.CompanionTheory.Ar.GR.submodule_eq_of_hasLen_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.submodule_eq_of_hasLen_eq <;> assumption)
