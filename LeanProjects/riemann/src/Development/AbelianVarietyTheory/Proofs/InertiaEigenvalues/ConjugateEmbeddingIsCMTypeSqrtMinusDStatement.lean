import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusD
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateEmbedding_isCMType_sqrtMinusD : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsCMType (phi H) ∧ ∀ g g', phi H g H.sqrtMinusD = phi H g' H.sqrtMinusD := by
  first | exact @GlobalTheory.LamTie.CMType.phi_cmType | exact GlobalTheory.LamTie.CMType.phi_cmType | (intros; apply GlobalTheory.LamTie.CMType.phi_cmType <;> assumption)
