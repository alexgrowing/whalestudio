import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAtTypes
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_compatibility_at_types : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), SumRepresentations.ConclusionG5 D → HG D.nd D.naut i → GoodR D.nd i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i → TameCharacterConditions D i → (∀ w ∈ D.nd.S i, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → (∀ x, ∃ P, D.naut.ptV i P = some x ∧ D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w = D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ P : D.naut.AV i, ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), D.naut.inePol (D.naut.locV i P w) σ = (Polynomial.X - 1) ^ D.R.nV) → PairedCharacterCondition.SetSQ i r := by
  first | exact @GlobalTheory.WildSetSQ.main | exact GlobalTheory.WildSetSQ.main | (intros; apply GlobalTheory.WildSetSQ.main <;> assumption)
