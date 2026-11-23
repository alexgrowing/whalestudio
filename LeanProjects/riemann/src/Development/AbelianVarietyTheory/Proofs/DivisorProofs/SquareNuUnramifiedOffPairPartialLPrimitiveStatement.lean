import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuUnramifiedOffPairPartialLPrimitive
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareNu_unramified_off_pair_partial_L_primitive : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → D.host.F = maximalRealSubfield D.host.E →
  ∀ (G : GridData L sc) (t : T) (i j : Fin D.R.m) (χ : (AE D)ˣ →* Circle), ChrEq χ (nuH G t i j) →
    GlobalTheory.LFun.UnrOff χ ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) ∧
    ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ∀ s : ℂ,
      GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL χ⁻¹ ((sfB G t : Finset (FinPl D)) : Set (FinPl D))) s (Λ s) := by
  first | exact @GlobalTheory.NuOffPair.main | exact GlobalTheory.NuOffPair.main | (intros; apply GlobalTheory.NuOffPair.main <;> assumption)
