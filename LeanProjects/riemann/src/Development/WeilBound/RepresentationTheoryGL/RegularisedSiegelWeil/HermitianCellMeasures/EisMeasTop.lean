import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralLeOfMinor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopX
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulLeftFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermScaleMain
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbEx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisMeas

namespace PositivityTheory.Rg.Rsw.Em

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

theorem eisMeas : IdemEx → BumpEx → Major → FixW → FixTh → ThProd → MuCell → FibEx → RCell → PosExt → ApproxId → EisMeas :=
  fun hI hB hM hW hT hP hC hF hR hE hA =>
  have hX := GlobalTheory.CompanionTheory.RswEmTop.topX
  have hRi := GlobalTheory.CompanionTheory.AlgRich.algRich hI hB hX
  have hS := GlobalTheory.CompanionTheory.SigL.main hI hX
  GlobalTheory.CompanionTheory.EisE.eisMeas hI hB hM hW hT hP hC hF hR hX hRi hS
    (GlobalTheory.CompanionTheory.OrbExist.orbEx hI hA (GlobalTheory.CompanionTheory.EisDens.dens_main hE) hX hRi (GlobalTheory.CompanionTheory.AlgStab.algStab hI) hS (GlobalTheory.CompanionTheory.HermSc.hermScale_main hI hX))

end PositivityTheory.Rg.Rsw.Em
