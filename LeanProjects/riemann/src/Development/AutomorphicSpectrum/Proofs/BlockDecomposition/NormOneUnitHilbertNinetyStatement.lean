import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneUnitHilbertNinety
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_one_unit_hilbert_ninety : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ c : w.adicCompletion E, cj w c = c → Valued.v c = 1 → ∃ s : w.adicCompletion E, Valued.v s = 1 ∧ cj w s * s = c := by
  first | exact @GlobalTheory.CompanionTheory.UnitNormLocal.exists_unit_norm_eq | exact GlobalTheory.CompanionTheory.UnitNormLocal.exists_unit_norm_eq | (intros; apply GlobalTheory.CompanionTheory.UnitNormLocal.exists_unit_norm_eq <;> assumption)
