import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable section
namespace GlobalTheory.MovedDict
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {U : Set T}

def frS (N : Std G U) : ∀ p : GlobalTheory.ChiGrid.Pair T, GL (Fin (G.pS p).rank) D.host.E
  | .chi i j => N.fr (.grid (i + 1) j)
  | .mu _ i j => N.fr (.grid i j)
  | .core i => N.fr (.core (i + 1))
  | .top _ j => N.fr (.top j)

def frT (N : Std G U) : ∀ p : GlobalTheory.ChiGrid.Pair T, GL (Fin (G.pT p).rank) D.host.E
  | .chi i j => N.fr (.grid i j)
  | .mu _ i j => N.fr (.grid i (j + 1))
  | .core i => N.fr (.core i)
  | .top _ j => N.fr (.top (j + 1))

def inV {n : ℕ} (B : GL (Fin n) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E) :=
  (B : Matrix (Fin n) (Fin n) D.host.E).mulVec '' (Λ : Set (Fin n → D.host.E))

end GlobalTheory.MovedDict
end
