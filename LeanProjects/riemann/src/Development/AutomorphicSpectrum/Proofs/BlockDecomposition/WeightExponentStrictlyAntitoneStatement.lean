import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_exponent_strictly_antitone : ∀ (n : ℕ) (l : Fin (n / 2) → ℤ), Cone l → StrictAnti (wexp n l) ∧ ∀ i, wexp n l (Fin.rev i) = -wexp n l i := by
  first | exact @GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev | exact GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev | (intros; apply GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev <;> assumption)
