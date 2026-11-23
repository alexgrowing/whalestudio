import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfFiniteProjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_of_finite_projective : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), Module.Finite R L → Module.Projective R L → Module.finrank Ω E = r → IsBaseChange Ω L.subtype → LocFree R r L.toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective | exact GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective <;> assumption)
