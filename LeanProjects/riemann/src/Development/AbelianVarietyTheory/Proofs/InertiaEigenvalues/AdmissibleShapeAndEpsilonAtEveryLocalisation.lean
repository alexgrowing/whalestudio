import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedLift
import Development.AutomorphicArithmetic.CyclotomicBounds.FiniteDimensionalRoots
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.admissible_shape_and_epsilon_at_every_localisation

theorem main : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible (D := D) i ∧ TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  intro D i
  refine ⟨fun w hw => ?_, GlobalTheory.TameFixedLift.main D.nd i⟩
  exact UpperTheory.KStar.Cyc.kw_le_roots D.host.toHostRaw (D.nbr i w hw)

end GlobalTheory.admissible_shape_and_epsilon_at_every_localisation
