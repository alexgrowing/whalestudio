import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryBoundOfInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDictionaryEventuallyLarge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryBoundOfInputsStatement

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
namespace GlobalTheory.SumSize
theorem sum_size_dictionary_of_local_bounds (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) : DictK := by
  obtain ⟨CF0, h⟩ := _root_.GlobalTheory.T.twisted_dictionary_correspondence hP hI
  refine ⟨CF0, fun CF hCF => ⟨0, fun ε C _ => ?_⟩⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  exact ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ =>
    hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt⟩
end GlobalTheory.SumSize
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_size_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK := by
  first | exact @_root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds | exact _root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds | (intros; apply _root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds <;> assumption)
end
