import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStandardAuxiliaryFramesAllRowGridsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardAuxiliaryFramesFitGridEndsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardAuxiliaryFramesGoodRowGridsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

theorem towerEx_of_depFixed : GlobalTheory.SepRows.DepFixed → GlobalTheory.Asc.TowerEx := by
  intro hd D hq T L μ0 hL sc G W M hM v
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_standardAuxiliaryFrames_allRowGrids D hq T L μ0 hL sc G W M hM
  exact ⟨F, GlobalTheory.T.standardAuxiliaryFrames_fit_grid_ends D hq T L μ0 hL sc G W M hM v F hF, lineLat F,
    GlobalTheory.T.standardAuxiliaryFrames_good_row_grids hd D hq T L μ0 hL sc G W M hM v F hF⟩

end GlobalTheory.AscFin
