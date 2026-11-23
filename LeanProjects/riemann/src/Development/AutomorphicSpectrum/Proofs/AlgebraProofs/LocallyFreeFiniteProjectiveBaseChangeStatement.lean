import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_finite_projective_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), LocFree R r L.toAddSubgroup → Module.Finite R L ∧ Module.Projective R L ∧ Module.finrank Ω E = r ∧ IsBaseChange Ω L.subtype := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main | exact GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main <;> assumption)
