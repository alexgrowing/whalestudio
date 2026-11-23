import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Formalism.SharpRestriction.LevelLetterCocycles.CongruenceAnnihilatesCharacterPart
import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory

theorem lemma_open_of_integrality (D : D7) (h41 : Formalism.MainNotions.SumRepresentations.Conclusion41 D) : TypePrimeCongruences.CongruenceModules.SupplierRemainingLemmas D :=
  fun i _ _ _ r ρ hr =>
    ⟨LargeLevelLemmas.span_lemma_clause i r (galois_condition_one_of D i r h41 hr),
      fun π _ _ => ⟨LargeLevelLemmas.eigenspace_lemma_clause i r ρ π, LargeLevelLemmas.relation_lemma_clause i r ρ π⟩⟩

theorem supplier_type_prime_all : ∀ D : D7, TypePrimeCongruences.TypePrimeConclusionsOfHypotheses D :=
  fun D hA => TypePrimeCongruences.CongruenceModules.supplier_of_choice_and_lemmas D hA.2.2.2 (lemma_open_of_integrality D hA.2.1)

end GlobalTheory
