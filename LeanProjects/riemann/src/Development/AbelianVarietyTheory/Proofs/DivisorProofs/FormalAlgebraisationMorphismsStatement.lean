import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalAlgebraisation_morphisms' : GlobalTheory.Published.FormalAlgebraisation.Morphisms := by
  first | exact @GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms | exact GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms | (intros; apply GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms <;> assumption)
