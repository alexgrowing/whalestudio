import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlternativeLocalComputationOfComponentsStatement
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.JacquetPiatetskiBoundHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompactBis

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.Jp

theorem jPos_of_idemEx : IdemEx → JPos := by
  intro _ D n r t hrt hr ψ hψ χ hχ hres nb hnb S
  have hB2 : SplitPlaceRankCutEigenvalue := GlobalTheory.T.split_place_rank_cut_of_alternative (GlobalTheory.T.alternative_local_computation_of_components GlobalTheory.T.iwasawa_decomposition_statement GlobalTheory.T.height_bound_statement GlobalTheory.T.uniform_boundedness_statement GlobalTheory.T.compactness_statement GlobalTheory.T.positivity_statement)
  obtain ⟨v, hvS, hpsi, τ, hchi⟩ := GlobalTheory.T.jacquet_piatetski_bound_holds D r ψ hψ χ hχ hres S
  obtain ⟨C, c, hK, hd, hc, hint⟩ := hB2 D n r t hrt hr ψ hψ nb hnb v hpsi τ
  refine ⟨v, hvS, C, c, hK, hd, hc, ?_⟩
  intro νv hH hP z f _ hlaw hinv g
  exact GlobalTheory.T.section_eigenfunction_maximal_compact D n χ nb hnb v τ hchi C νv hH z (c z) (hint νv hH hP z) f hlaw hinv g

end GlobalTheory.CompanionTheory.Jp
