import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses3
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PDivisibleGroupsOverOC
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaNumberSU
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB

namespace GlobalTheory.CovTop

structure Slim : Prop where

  arForm : GlobalTheory.Published.ArFormExists

  arMix : GlobalTheory.Published.ArMix

  htProj : GlobalTheory.Published.HeightProjection

  chern : GlobalTheory.Published.ChernDegreeComplex

  volGe : GlobalTheory.Published.VolGe

  hs : GlobalTheory.Published.ArithHilbertSamuel

  kv : GlobalTheory.Published.KawamataViehweg

  nefProd : GlobalTheory.Published.NefProductNonneg

  nefRR : GlobalTheory.Published.NefRiemannRoch

  l2 : GlobalTheory.Published.L2ExtensionLogCanonical

  nadel : GlobalTheory.Published.NadelVanishingPair

  nonKlt : GlobalTheory.Published.IsolatedNonKltDivisor

  princ : GlobalTheory.Published.Principalisation

  chowCut : GlobalTheory.Published.ChowFormHyperplaneSection

  dr : GlobalTheory.Published.AbelianDeRhamStructure

  crys : GlobalTheory.Published.CrystallineDeRham

  dual : GlobalTheory.Published.DualAbelianScheme

  poinc : GlobalTheory.Published.PoincareDeRhamDuality

  lift : GlobalTheory.Published.AbelianLifting

  alg : GlobalTheory.Published.FormalAlgebraisation

  canExt : GlobalTheory.Published.DeRhamCanonicalExtension

  prism : GlobalTheory.Published.PrismaticDieudonneHodge

  pdiv : GlobalTheory.Published.PDivisibleGroupsOverOC

  tam : GlobalTheory.Published.TamagawaNumberSU

  ray : GlobalTheory.Published.RayClassFieldSt

  approx : GlobalTheory.Published.StrongApproxSU

  green : GlobalTheory.Published.GreenSeriesSt

  good : GlobalTheory.Published.GoodChernNumbers

  push : GlobalTheory.Published.FlagPushForward

  homExt : GlobalTheory.Published.SemiAbelianHomExtension

  sieg : GlobalTheory.Published.SiegelToroidalIntegral

  fan : GlobalTheory.Published.ToroidalChartsForFan

structure Idle : Prop where

  p7 : GlobalTheory.Published.GaussBonnetUnitary

  p9 : GlobalTheory.Published.WeberRayFieldSt

  p10 : GlobalTheory.Published.ComplexMultiplicationJSt

  p11 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt

  p15 : GlobalTheory.Published.CuspidalMirabolic

  p17 : GlobalTheory.Published.CanonKeySt

  p21 : GlobalTheory.Published.SuccMinTransference

  p24 : GlobalTheory.Published.PolExtSt

  q5 : GlobalTheory.Published.PrismaticDieudonne

  q14 : GlobalTheory.Published.DbarCompleteKaehler

  q17 : GlobalTheory.Published.SerreTateGoodReductionSt

  q19 : GlobalTheory.Published.AbelianDieudonne

  g3 : GlobalTheory.Published.DeRhamVectorExtension

end GlobalTheory.CovTop
