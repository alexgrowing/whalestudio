import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable section
namespace GlobalTheory.MovedDict
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}

def srcLat (S : GridChoice W Set.univ) : ∀ p : GlobalTheory.ChiGrid.Pair T, FinPt G p.small → FinPt G p.big →
    Submodule (𝓞 D.host.E) (Fin (G.pS p).rank → D.host.E)
  | .chi i j, _, y => GlobalTheory.SumSize.latAt S (.grid (i + 1) j) y
  | .mu _ i j, x, _ => GlobalTheory.SumSize.latAt S (.grid i j) x
  | .core i, _, y => GlobalTheory.SumSize.latAt S (.core (i + 1)) y
  | .top _ j, x, _ => GlobalTheory.SumSize.latAt S (.top j) x

def tgtLat (S : GridChoice W Set.univ) : ∀ p : GlobalTheory.ChiGrid.Pair T, FinPt G p.small → FinPt G p.big →
    Submodule (𝓞 D.host.E) (Fin (G.pT p).rank → D.host.E)
  | .chi i j, x, _ => GlobalTheory.SumSize.latAt S (.grid i j) x
  | .mu _ i j, _, y => GlobalTheory.SumSize.latAt S (.grid i (j + 1)) y
  | .core i, x, _ => GlobalTheory.SumSize.latAt S (.core i) x
  | .top _ j, _, y => GlobalTheory.SumSize.latAt S (.top (j + 1)) y

end GlobalTheory.MovedDict
end
