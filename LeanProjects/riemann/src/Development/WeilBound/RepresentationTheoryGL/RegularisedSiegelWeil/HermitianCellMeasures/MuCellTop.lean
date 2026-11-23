import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.MuCellOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDivRp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSmulQuot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NullCOfInvM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFormulaOfInvM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianFields
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnTau
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PtMulComplSelf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteBadScalar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingHomMulSubEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixEqBlockDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NpowHalfAddHalf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSMx

namespace PositivityTheory.Rg.Rsw.Cell

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

theorem muCell : HtExist → IdemEx → MuCell := fun hH hI =>
  have hU := GlobalTheory.CompanionTheory.UnitCell.unitCrit hI
  have hA := GlobalTheory.CompanionTheory.CellTop.cellAlg hI
  muCell_of GlobalTheory.CompanionTheory.RswCell.riesz (GlobalTheory.CompanionTheory.RswCell.NullCompl.nullC_of_invM GlobalTheory.CompanionTheory.RswCellInv.invM) (GlobalTheory.CompanionTheory.RswCell.cellFormula_of_invM GlobalTheory.CompanionTheory.RswCellInv.invM) hA (GlobalTheory.CompanionTheory.CellDecomp.decomp hI)
    (GlobalTheory.CompanionTheory.CellFew.fewC hI hU (GlobalTheory.CompanionTheory.MoveCell.move_of_unitCrit hU) (GlobalTheory.CompanionTheory.SmallRatCell.smallRat hI) hA) (GlobalTheory.CompanionTheory.SetCell.setC hH) GlobalTheory.CompanionTheory.RswTop.topC

end PositivityTheory.Rg.Rsw.Cell
