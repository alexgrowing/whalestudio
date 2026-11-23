import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicCharacterOfAdm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_character_of_adm : ∀ D : D7, SumRepresentations.adm2 D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D := by
  first | exact @GlobalTheory.AlgCharFromGal.main | exact GlobalTheory.AlgCharFromGal.main | (intros; apply GlobalTheory.AlgCharFromGal.main <;> assumption)
