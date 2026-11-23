import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenerationAlongInvariants
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generation_along_invariants : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun | exact GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun <;> assumption)
