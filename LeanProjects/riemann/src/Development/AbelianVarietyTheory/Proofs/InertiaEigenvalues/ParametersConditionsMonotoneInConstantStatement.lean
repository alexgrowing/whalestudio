import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SizeConditionsMonotoneInConstant
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizeConditions_mono : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C C' : ℝ), C ≤ C' → 0 ≤ C' → (StarF L X.ρ C → StarF L X.ρ C') ∧ (StarH L C → StarH L C') ∧ (KillingConditions.BBLe L X C → KillingConditions.BBLe L X C') ∧ (TwistedPlaces.ParametersPolynomiallyBounded L C P → TwistedPlaces.ParametersPolynomiallyBounded L C' P) := by
  first | exact @GlobalTheory.NLinkMono.main | exact GlobalTheory.NLinkMono.main | (intros; apply GlobalTheory.NLinkMono.main <;> assumption)
