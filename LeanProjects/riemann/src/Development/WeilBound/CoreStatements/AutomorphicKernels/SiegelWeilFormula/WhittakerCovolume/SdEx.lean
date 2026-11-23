import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelAlg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianAdelesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianTuplesStatement

namespace PositivityTheory.SiegelWeilFormula.KWhit

theorem sdEx : SdEx := by
  intro F E _ _ _ _ _ σ hcm M J hJ ψ hψ n
  exact ⟨GlobalTheory.T.exists_selfdual_measure_hermitian_tuples F E σ hcm M J hJ ψ hψ n, GlobalTheory.T.exists_selfdual_measure_hermitian_adeles F E σ hcm ψ hψ n⟩

end PositivityTheory.SiegelWeilFormula.KWhit
