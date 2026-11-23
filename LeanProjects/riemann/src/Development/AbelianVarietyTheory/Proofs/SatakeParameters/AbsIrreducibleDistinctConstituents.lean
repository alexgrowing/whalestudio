import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtensionStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem abs_irreducible_distinct_constituents : ∀ (D : D7), SumRepresentations.Conclusion41 D → GlobalTheory.SplitCoef.OSplit D → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → AbsIrreducibleDistinct D i r := by
  intro D h32 hS i r hr
  obtain ⟨K', hK', hA, _, hK⟩ := (((h32 i).2.2 r hr).2.2.1).1
  exact GlobalTheory.T.absIrr_distinct_constituents_after_extension D i r (hS i) hr K' (algebraMap (Kf D.nd i) K') (fun x => (hK x).2)

end GlobalTheory
