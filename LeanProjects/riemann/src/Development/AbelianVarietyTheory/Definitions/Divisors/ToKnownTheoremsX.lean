import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesY
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LogResolutionProjectiveLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointDimensionLtProjectiveLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower

namespace GlobalTheory.CovTop

structure HypothesesXH : Prop where

  toClassicalTheoremsX : HypothesesX

  mb : GlobalTheory.Published.MoretBaillyModel

  arr : GlobalTheory.Published.ArithRiemannRoch

  cube : GlobalTheory.Published.CubeTheorem

  dual : GlobalTheory.Published.DualAbelianScheme

  logres : GlobalTheory.Published.AnalyticLogResolution

  andim : GlobalTheory.Published.AnalyticSetDimension

  conj : GlobalTheory.Published.ConjugateFiltration

  ray : GlobalTheory.Published.RaynaudExtension

  orth : GlobalTheory.Published.GrothendieckOrthogonality

  y : GlobalTheory.CovHt.HypothesesY

  btd : GlobalTheory.Published.BarsottiTateDieudonne

instance : Coe HypothesesXH HypothesesX := ⟨HypothesesXH.toClassicalTheoremsX⟩

theorem HypothesesXH.ks (h : HypothesesXH) : GlobalTheory.Published.ToroidalForFanKS := h.toClassicalTheoremsX.ks

theorem HypothesesXH.lie (h : HypothesesXH) : GlobalTheory.Published.SemiAbelianLieSeminegative := h.toClassicalTheoremsX.lie

theorem HypothesesXH.green (h : HypothesesXH) : GlobalTheory.Published.GreenCuspidal := h.toClassicalTheoremsX.green

theorem HypothesesXH.sep (h : HypothesesXH) : GlobalTheory.Published.PointSeparationPair := h.toClassicalTheoremsX.sep

end GlobalTheory.CovTop
