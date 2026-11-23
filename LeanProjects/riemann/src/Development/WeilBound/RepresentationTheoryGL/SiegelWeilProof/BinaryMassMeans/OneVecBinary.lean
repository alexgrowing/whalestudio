import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SiegelDensitiesLowAOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquidistributionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMulStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocompactnessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMassFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfPartsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormulaStatement
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.SingleRowSide.Srside
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfPartsStatement

namespace PositivityTheory.Rg.Mass

theorem e1 : E1 :=
  GlobalTheory.T.one_vector_formula_of_parts (GlobalTheory.T.vector_length_formula_of_parts GlobalTheory.T.cocompactness GlobalTheory.T.local_mass_formula) GlobalTheory.T.similitude_invariance GlobalTheory.T.hasse_principle
    (GlobalTheory.T.counting_formula GlobalTheory.T.test_function_exists (GlobalTheory.T.left_side_formula GlobalTheory.T.equidistribution GlobalTheory.T.cocompactness)
      (PositivityTheory.Rg.Mass.LiteralAutomorphy.srside (GlobalTheory.T.mean_value_formula GlobalTheory.T.equidistribution GlobalTheory.T.counting_bound_alt) GlobalTheory.T.local_mass_formula))

theorem oneVecBinary : PositivityTheory.PfSWUS.HMass.OneVecBinary := by
  intro F E _ _ _ _ _ σ hc M J hJ hM hA T hT hd
  subst hM
  exact e1 F E σ hc J hJ (fun x hx => by_contra fun h => hA x h hx) T hT hd

end PositivityTheory.Rg.Mass
