import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonZeroDivisorOfDenseOfStrict
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.ComplReg

theorem isCompl_nonZeroDivisor : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T),
    IsCompl π g → π ∈ nonZeroDivisors B → g π ∈ nonZeroDivisors T := by
  intro B _ T _ π g hC hπ
  exact nonZeroDivisor_of_dense_of_strict π g hC.compl.toIsHausdorff hC.surj hC.inj hπ

end GlobalTheory.CompanionTheory.ComplReg
