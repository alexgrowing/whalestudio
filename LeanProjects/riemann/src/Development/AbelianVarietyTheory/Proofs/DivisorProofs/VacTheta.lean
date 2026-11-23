import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumIntegral

noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG)

namespace GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

structure Frame (P : Pair D cc δ t0 Q) where

  A : HSp D

  B : HSp D
  rkA : A.rank = P.a
  rkB : B.rank = P.d

  ιA : Formalism.MainNotions.StandardLatticesGL3.GA D P.a →* GA D A

  ιB : Formalism.MainNotions.StandardLatticesGL3.GA D P.d →* GA D B

  KA : Subgroup (GL (Fin A.rank) (Lev.EAf D))

  KB : Subgroup (GL (Fin B.rank) (Lev.EAf D))

  m : Measure (GA D A)

  mH : Measure (GA D B)

structure IsFrame (P : Pair D cc δ t0 Q) (Y : Frame P) : Prop where
  gramA : Y.A.gram = 1
  gramB : Y.B.gram = 1
  defA : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace Y.A
  defB : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace Y.B
  injA : Function.Injective Y.ιA
  injB : Function.Injective Y.ιB
  rangeA : Y.ιA.range = GfC Y.A
  rangeB : Y.ιB.range = GfC Y.B
  ratA : ∀ x, (∃ γ ∈ GQ Y.A, finHom Y.A γ = finHom Y.A (Y.ιA x)) ↔ x ∈ ratG D P.a
  ratB : ∀ h, (∃ γ ∈ GQ Y.B, finHom Y.B γ = finHom Y.B (Y.ιB h)) ↔ h ∈ ratG D P.d
  levA : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.A Y.KA
  levB : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.B Y.KB
  levA_iff : ∀ x, Lev.finE Y.A (Y.ιA x) ∈ Y.KA ↔ x ∈ intG D P.a
  levB_iff : ∀ h, Lev.finE Y.B (Y.ιB h) ∈ Y.KB ↔ h ∈ P.J
  haarA : Y.m.IsHaarMeasure
  haarB : Y.mH.IsHaarMeasure
  measA : ∃ 𝓕, Links.IsMeasDef Y.A Y.KA Y.m 𝓕
  measB : ∃ 𝓕, Links.IsMeasDef Y.B Y.KB Y.mH 𝓕

structure Data (P : Pair D cc δ t0 Q) extends Frame P where

  ψ : AddChar (AF D.host.F) ℂ

  θ : InfFam D

  χA : (AE D)ˣ →* Circle

  χB : (AE D)ˣ →* Circle

  om : GlobalTheory.Core.Rk.IP.WRep A B

  vac : WO A B → ℂ

  c₁ : ℂ

namespace Data

variable {P : Pair D cc δ t0 Q} (X : Data P)

def var (k : Formalism.MainNotions.GL3Theta.Idx D P.a P.d) : FVar D X.B.rank X.A.rank :=
  (k.1, Fin.cast X.rkB.symm k.2.1, Fin.cast X.rkA.symm k.2.2)

def fock (T : Tup D P.a P.d P.n) : WO X.A X.B → ℂ :=
  pureTensorL (aPlusAll (heisO X.ψ X.A X.B) X.θ (fun _ => cplxO 1 1) (fun _ => 1) (fun _ => 1)) X.vac
    (MvPolynomial.rename X.var (minorPol D T))

def lift (T : Tup D P.a P.d P.n) : GA D X.B → ℂ := GlobalTheory.Core.Rk.IP.up X.om X.m (X.fock T) 1

end Data

structure IsWeilOf (P : Pair D cc δ t0 Q) (X : Data P) : Prop where
  inf : IsInfFam X.θ
  weil : IsWeilDatumO X.ψ X.A X.B X.χA X.χB X.om
  vac_theta : IsThetaFunO X.ψ X.A X.B X.vac
  vac_fock : ∀ τ, IsFockVacAt (heisO X.ψ X.A X.B) X.θ τ (cplxO 1 1) X.vac
  c₁_ne : X.c₁ ≠ 0
  ker : ∀ x h T, thetaKO X.om (X.ιA x) (X.ιB h) (X.fock T) = X.c₁ * P.term x h T

  fixA : ∀ k ∈ intG D P.a, ∀ T, X.om (X.ιA k, 1) (X.fock T) = X.fock T

  eigB : ∀ j ∈ P.J, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ T, X.om (1, X.ιB j) (X.fock T) = c • X.fock T

  infB : ∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))

def IsDict (P : Pair D cc δ t0 Q) (X : Data P) : Prop := IsFrame P X.toFrame ∧ IsWeilOf P X

end GlobalTheory.NormDict
