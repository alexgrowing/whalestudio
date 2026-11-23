import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldTwoVocabulariesDictionary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localField_two_vocabularies_dictionary : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F], resCard F = GroundTheory.LocalField.residueCard F ∧ (∀ x : Fˣ, ord F x = GroundTheory.LocalField.ord (x : F)) ∧ (∀ χ : Fˣ →* ℂˣ, IsUnram χ ↔ GroundTheory.LocalField.IsUnramifiedChar χ) ∧ (∀ (χ : Fˣ →* ℂˣ) (a : ℕ), HasExponent χ a → GroundTheory.LocalField.quasiCharConductor χ = a) ∧ ∀ (ψ : AddChar F Circle) (c : Fˣ), HasConductor ψ c → GroundTheory.LocalField.addCharConductor ψ = ord F c := by
  first | exact @GlobalTheory.DelGlob.localVocabularyDictionary | exact GlobalTheory.DelGlob.localVocabularyDictionary | (intros; apply GlobalTheory.DelGlob.localVocabularyDictionary <;> assumption)
