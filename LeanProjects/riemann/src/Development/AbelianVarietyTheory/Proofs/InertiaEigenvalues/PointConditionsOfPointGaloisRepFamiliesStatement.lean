import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamilies
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.SemisimpleDecompositionOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (ρ i π) ∧ IsSSRep (rhoChiK D i (ρ i π)) ∧ EmbeddingTypes.ambBlock i (r i) (ρ i) π ∧ TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (r i) (ρ i) π := by
  first | exact @GlobalTheory.PointConditions.main | exact GlobalTheory.PointConditions.main | (intros; apply GlobalTheory.PointConditions.main <;> assumption)
