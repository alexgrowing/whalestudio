import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteRowOfDictionaryDepth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KernelConjMeanPairingStandardKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteRowOfDictionaryDepthStatement

section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.SumSize.OppConj
namespace GlobalTheory.SumSize.OppConj
theorem archimedean_sum_size_opposite_conjugate : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfRowK :=
  fun hP hI hD hDp => infRowK_of (_root_.GlobalTheory.T.conj_mean_kernel_pairing hP hI hD hDp)
end GlobalTheory.SumSize.OppConj
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_size_bound_opposite_conjugation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfRowK := by
  first | exact @_root_.GlobalTheory.SumSize.OppConj.archimedean_sum_size_opposite_conjugate | exact _root_.GlobalTheory.SumSize.OppConj.archimedean_sum_size_opposite_conjugate | (intros; apply _root_.GlobalTheory.SumSize.OppConj.archimedean_sum_size_opposite_conjugate <;> assumption)
end
