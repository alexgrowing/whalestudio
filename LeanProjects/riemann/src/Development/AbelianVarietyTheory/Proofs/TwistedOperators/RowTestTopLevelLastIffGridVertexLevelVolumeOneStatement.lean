import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestTopLevelLastIffGridVertexLevelVolumeOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_topLevel_last_iff_gridVertexLevelVolumeOne : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ β (h : D.R.m - 1 < D.R.m), 2 ≤ D.R.m → ∀ (k : FinPt ch.G (.top (D.R.m - 1))),
    finG (ch.G.V (.top (D.R.m - 1))) k ∈ ch.S.toGridChoice.levTop t Φ β (D.R.m - 1) h ↔
      finG (ch.G.V (.top (D.R.m - 1))) k ∈ levJ ch.G t (.top (D.R.m - 1)) := by
  first | exact @GlobalTheory.LastLevUnit.levTop_iff_levJ | exact GlobalTheory.LastLevUnit.levTop_iff_levJ | (intros; apply GlobalTheory.LastLevUnit.levTop_iff_levJ <;> assumption)
