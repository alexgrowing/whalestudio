import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

noncomputable section

namespace Formalism.MainNotions.AdmissibleBoundsFromSource

export Formalism.MainNotions.S.UnitaryVolumeMass (f3 Kpp)

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain
open scoped InnerProductSpace nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Letters

variable (D : D7) (large₂ : SizeData₂ D)

def Gam : ℝ := (D.mem D.u₀).A.GamP

def du (u : D.what₂.Word) : ℝ := D.duS u

def Dall : ℝ := D.what₂.Dall

def Dst : ℝ := D.what₂.Dstar

def eta0 : ℝ := large₂.sc.b ^ (-(6 : ℝ))

def xK : ℝ := Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))
end Letters

section Hyp

variable (D : D7) (large₂ : SizeData₂ D)

def hyp (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  StandingNumericalData D C0 ∧ StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ 1 ≤ C0

def GamDef (CE CN : ℝ) : Prop := max CE CN + 1 ≤ large₂.CGam

def DiagonalKernelBoundParameters (Cl Cg CT : ℝ) : Prop :=
  UnitaryVolumeMass.KTwoParameterConditions D large₂ Cl Cg CT

def WordPairStandingData (u u' : D.what₂.Word) : Prop :=
  1 ≤ D.R.rS ∧
  (Lat.Tu D u).Prime ∧ (Lat.Tu D u').Prime ∧ 3 ≤ Lat.Tu D u ∧ 3 ≤ Lat.Tu D u' ∧
  Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) ∧ Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u') ∧
  (D.host.g 0).Prime ∧ (D.host.g 1).Prime ∧ D.host.g 0 ≠ D.host.g 1 ∧
  (∀ i, Lat.SplitsCompletely (E := D.host.E) (D.host.g i)) ∧
  Nat.Coprime (Lat.gS D) (Lat.Tu D u * Lat.Tu D u') ∧ Lat.Tu D u ≡ Lat.Tu D u' [MOD Lat.gS D]

def WordPairParameters (u u' : D.what₂.Word) (Cl A : ℝ) : Prop :=
  WordPairStandingData D u u' ∧
  Tr D u' / Tr D u ≤ A ∧ Tr D u / Tr D u' ≤ A ∧
  Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) ≤ (D.R.k : ℝ) * Real.log D.R.k ∧
  Real.log (D.R.f : ℝ) ^ 2 ≤ A * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ∧
  Real.log (D.R.f : ℝ) ≤ A * (D.R.rS : ℝ) ^ 2 ∧
  ∀ τ, vand (uS D u' τ) ≤ A ^ D.R.k * vand (uS D u τ) ∧ vand (uS D u τ) ≤ A ^ D.R.k * vand (uS D u' τ)

def CountTheoremHypotheses (n0 : ℕ) (A C cb : ℝ) : Prop :=
  NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 ∧
  n0 ≤ D.R.r ∧ (D.R.rS + 1) ^ 2 ≤ D.R.r ∧
  Real.log (Real.log D.host.rdE) ≤ (D.R.r : ℝ) ∧
  (∀ (τ : D.what₂.Tau) (i : Fin D.R.r), |lamS D.R (D.hc τ) i| ≤ large₂.sc.b ^ 2) ∧
  gg D ≤ large₂.sc.b ^ A ∧ 4 * D.R.r < D.host.g 0 ∧ SplitsE D (D.host.g 0) ∧
  (∀ τ : D.what₂.Tau, Formalism.QuantumDeterminants.GapAtLeast (epsS D.R) (lamS D.R (D.hc τ))
    (C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (large₂.sc.b * D.host.rdE))) ∧
  Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.r : ℝ) ∧ 2 ≤ large₂.sc.b ∧
  Real.log (Real.log large₂.sc.b) ≤ cb * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)

end Hyp

structure AdmC where

  A5 : ℝ
  cL : ℝ

  cN : ℝ
  CN : ℝ

  CE : ℝ

  CA : ℝ
  CA' : ℝ
  Ce : ℝ

  n7 : ℕ
  A7 : ℝ
  C7 : ℝ
  cb7 : ℝ
  c7 : ℝ

  ep0 : ℝ
  CV : ℝ

  C1 : ℝ
  C2 : ℝ
  c5 : ℝ

def AdmC.Ok (ca : AdmC) (Cg : ℝ) : Prop :=
  1 ≤ ca.A5 ∧ ca.C1 ≤ ca.A5 ∧ ca.C2 ≤ ca.A5 ∧ 0 < ca.cL ∧ 0 < ca.cN ∧ 0 ≤ ca.CN ∧
  0 ≤ ca.CE ∧ 0 < ca.CA ∧ 0 < ca.CA' ∧ 0 ≤ ca.Ce ∧ 2 * Cg ≤ ca.A7 ∧ 0 < ca.C7 ∧ 0 < ca.cb7 ∧ 0 < ca.c7 ∧
  0 < ca.ep0 ∧ ca.ep0 < 1 / 2 ∧ 0 ≤ ca.CV ∧ 0 < ca.c5

section admitted

variable (D : D7) (large₂ : SizeData₂ D)

def adm1 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.cExp D

def adm2 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.cIdOne D

def adm3 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → DiagonalKernelBoundParameters D large₂ Cl Cg CT → UnitaryVolumeMass.cK2off D

def ArchimedeanSignatureMatching (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.c2aG D

def adm5 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → DiagonalKernelBoundParameters D large₂ Cl Cg CT →
    ∀ u : D.what₂.Word, hsNormSq (Kpp D u u) ≤ du D u * xK D

def adm6 (C0 C' Cl Cg cb Cu cT CT A c : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → ∀ u u' : D.what₂.Word, WordPairParameters D large₂ u u' Cl A → UnitaryVolumeMass.LoopPairSumBound D u u' c

def adm7 (C0 C' Cl Cg cb Cu cT CT c C : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.NonGenericKernelBound D large₂ c C

def adm8 (C0 C' Cl Cg cb Cu cT CT C : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.GenericScalarPairSum D large₂ C

def adm9 (C0 C' Cl Cg cb Cu cT CT CA CA' Ce : ℝ) : Prop :=
  let N : ℝ := NA D
  let r : ℝ := D.R.rS
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u u' : D.what₂.Word, u ≠ u' → ∀ (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D),
    IsLocA D u u' x → IsLatGLOB D L →
    (∀ τ, IsCutS (uS D u τ) (uS D u' τ) (Set.Icc (x τ).a (x τ).b) ∧
      CA * ((D.R.k : ℝ) * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ (x τ).b - (x τ).a ∧
      (x τ).a ≤ (x τ).a1 ∧ (x τ).b1 ≤ (x τ).b ∧ N ^ 3 / 2 ≤ (x τ).b1 - (x τ).a1) →
    (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ) ≤ 1 → CA' ≤ ThA D CA u u' x L →
    genScal D u u' ≤ (1 + CA * (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ)) * (1 + eSum D Ce) *
      f3 D * du D u * du D u' / Dst D

def adm10 (n0 : ℕ) (A C cb c : ℝ) : Prop := CountTheoremHypotheses D large₂ n0 A C cb →
  |Dall D - Dst D| ≤ Real.exp (-(c * D.R.r * D.R.f * Real.log D.R.r)) * Dst D

def WeylDimensionFormula (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u τ, (dimPiU D.R.k (uS D u τ) : ℝ) = vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)

def FilteredProjectionCriterion (C0 C' Cl Cg cb Cu cT CT ep0 : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ τ, (1 - ep0) * vand (lamSH D.R (D.hc τ)) ≤ VV D τ

def VandermondeUpperBound (C0 C' Cl Cg cb Cu cT CT C : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ τ, VV D τ ≤ Real.exp (C * D.R.k * D.R.m * large₂.sc.L) * vand (lamSH D.R (D.hc τ))

def adm11 (C0 C' Cl Cg cb Cu cT CT ep0 C : ℝ) : Prop :=
  WeylDimensionFormula D large₂ C0 C' Cl Cg cb Cu cT CT ∧ FilteredProjectionCriterion D large₂ C0 C' Cl Cg cb Cu cT CT ep0 ∧
    VandermondeUpperBound D large₂ C0 C' Cl Cg cb Cu cT CT C

def adm12 : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

def adm13 (C0 C' Cl Cg cb Cu cT CT C1 C2 c5 CA : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  UnitaryVolumeMass.cTvA D ∧ UnitaryVolumeMass.cTvB D C1 ∧ UnitaryVolumeMass.cTvC D C2 ∧ UnitaryVolumeMass.cTvF D large₂ c5 CA

def adm14 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u u' : D.what₂.Word,
    (∀ t : D.s.Term u u', ¬ D.s.relevant t → D.s.aTerm u u' t = 0) ∧
    (∀ t : D.s.Term u u', D.s.isId t → D.s.Gterm t = 0) ∧
    (∀ p : D.s.Pair u u', D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → 1 ≤ D.s.s0 p)

def adm15 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u u' : D.what₂.Word, Summable (fun p : D.s.Pair u u' => ‖D.s.pval p‖)

def fixAt (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    Submodule ℂ ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :=
  (D.mem u).A.Mu0 ⊓ ⨅ c : ((D.mem u).A.Fv v)ˣ, LinearMap.ker ((D.mem u).A.rhoT v c - LinearMap.id)

def adm16 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ (u : D.what₂.Word) (v : (D.mem u).A.vT), (Module.finrank ℂ (fixAt D u v) : ℝ) = du D u / (Tr D u - 1)

def Adm1 (C0 C' Cl Cg cb Cu cT CT : ℝ) (ca : AdmC) : Prop :=
  adm1 D large₂ C0 C' Cl Cg cb Cu cT CT ∧ adm2 D large₂ C0 C' Cl Cg cb Cu cT CT ∧
    adm3 D large₂ C0 C' Cl Cg cb Cu cT CT ∧ ArchimedeanSignatureMatching D large₂ C0 C' Cl Cg cb Cu cT CT ∧ adm5 D large₂ C0 C' Cl Cg cb Cu cT CT ∧
    adm6 D large₂ C0 C' Cl Cg cb Cu cT CT ca.A5 ca.cL ∧ adm7 D large₂ C0 C' Cl Cg cb Cu cT CT ca.cN ca.CN ∧
    adm8 D large₂ C0 C' Cl Cg cb Cu cT CT ca.CE ∧ adm9 D large₂ C0 C' Cl Cg cb Cu cT CT ca.CA ca.CA' ca.Ce ∧
    adm11 D large₂ C0 C' Cl Cg cb Cu cT CT ca.ep0 ca.CV ∧ adm12 ∧
    adm13 D large₂ C0 C' Cl Cg cb Cu cT CT ca.C1 ca.C2 ca.c5 ca.CA ∧ adm14 D large₂ C0 C' Cl Cg cb Cu cT CT ∧
    adm15 D large₂ C0 C' Cl Cg cb Cu cT CT

def admitted (C0 C' Cl Cg cb Cu cT CT : ℝ) (ca : AdmC) : Prop :=
  Adm1 D large₂ C0 C' Cl Cg cb Cu cT CT ca ∧ adm10 D large₂ ca.n7 ca.A7 ca.C7 ca.cb7 ca.c7 ∧
    adm16 D large₂ C0 C' Cl Cg cb Cu cT CT

end admitted

section Conclusion₂

variable (D : D7) (large₂ : SizeData₂ D)

def Conclusion1 : Prop :=
  (∀ u u' : D.what₂.Word, u ≠ u' → Kpp D u u' = 0) ∧
  (∀ u, hsNormSq (Kpp D u u) ≤ du D u * xK D) ∧
  (∀ u u' : D.what₂.Word, u ≠ u' →
    hsNormSq (Kmat D.s u u' - Kpp D u u') ≤ (1 + eta0 D large₂) * du D u * du D u' / Dst D) ∧
  (∀ u, hsNormSq (Kmat D.s u u - Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) ≤
    Gam D * du D u ^ 2 / Dst D)

def rkCoPi (u : D.what₂.Word) : ℝ :=
  Module.finrank ℂ (LinearMap.range ((ContinuousLinearMap.id ℂ (D.s.Cu u) - PiU D u : D.s.Cu u →L[ℂ] D.s.Cu u) :
    D.s.Cu u →ₗ[ℂ] D.s.Cu u))

def Q0 (Ws : Finset D.what₂.Word) (Pi : D.s.HH →L[ℂ] D.s.HH) : D.s.HH →L[ℂ] D.s.HH :=
  ∑ u ∈ Ws, (((c0 D.s u)⁻¹ : ℝ) : ℂ) •
    (Pi.comp ((D.s.Pu u).comp ((PiU D u).comp ((ContinuousLinearMap.adjoint (D.s.Pu u)).comp Pi))))

def trH (A : D.s.HH →L[ℂ] D.s.HH) : ℝ := (LinearMap.trace ℂ D.s.HH (A : D.s.HH →ₗ[ℂ] D.s.HH)).re

def rkH (A : D.s.HH →L[ℂ] D.s.HH) : ℝ :=
  Module.finrank ℂ (LinearMap.range (A : D.s.HH →ₗ[ℂ] D.s.HH))

def RR (Ws : Finset D.what₂.Word) : ℝ := ∑ u ∈ Ws, du D u

def sg (Ws : Finset D.what₂.Word) : ℝ := Dst D / RR D Ws

def eF (C0 : ℝ) : ℝ := 2 * C0 / Gam D + 2 * xK D

def AF (C0 : ℝ) (Ws : Finset D.what₂.Word) : ℝ :=
  1 + eta0 D large₂ + (1 + Real.sqrt (eF D C0)) ^ 2 * sg D Ws

def dec (Ws : Finset D.what₂.Word) (hW : Ws.Nonempty) : ℝ :=
  2 * D.R.f / Ws.inf' hW (fun u => Tr D u)

def BF (C0 del : ℝ) (Ws : Finset D.what₂.Word) (hW : Ws.Nonempty) : ℝ :=
  1 - Real.sqrt (eF D C0) - dec D Ws hW - Real.sqrt (dec D Ws hW * eF D C0) -
    Real.sqrt (del * AF D large₂ C0 Ws)

def projection_sandwich_lattice : Prop := ∀ u : D.what₂.Word, rkCoPi D u ≤ 2 * D.R.f * du D u / Tr D u

def Conclusion2Family (C0 : ℝ) : Prop :=
  ∀ (Ws : Finset D.what₂.Word) (hW : Ws.Nonempty) (del : ℝ) (Pi : D.s.HH →L[ℂ] D.s.HH)
      (SH : Submodule ℂ D.s.HH), 0 ≤ del → IsOrthProjOnto Pi SH →
      rkH D (ContinuousLinearMap.id ℂ D.s.HH - Pi) ≤ del * Dst D →
      0 < BF D large₂ C0 del Ws hW →
    BF D large₂ C0 del Ws hW * RR D Ws ≤ trH D (Q0 D Ws Pi) ∧
    trH D ((Q0 D Ws Pi).comp (Q0 D Ws Pi)) ≤
      (Dall D / Dst D) * AF D large₂ C0 Ws * (BF D large₂ C0 del Ws hW) ^ (-2 : ℤ) * trH D (Q0 D Ws Pi) ^ 2 /
        rkH D Pi

def Conclusion2 (C0 : ℝ) : Prop := projection_sandwich_lattice D ∧ Conclusion2Family D large₂ C0

def PointsLemma (C0 C : ℝ) : Prop :=
  ∀ (Ws : Finset D.what₂.Word) (hW : Ws.Nonempty) (del : ℝ), 0 ≤ del → del ≤ 1 / 100 → sg D Ws ≤ 1 / 100 →
    let η := C * sg D Ws + C * Real.sqrt del + large₂.sc.b ^ (-(5 : ℝ))
    0 < BF D large₂ C0 del Ws hW ∧ 1 - BF D large₂ C0 del Ws hW ≤ η ∧
      (Dall D / Dst D) * AF D large₂ C0 Ws * (BF D large₂ C0 del Ws hW) ^ (-2 : ℤ) - 1 ≤ η

def aux₃ : Prop := Conclusion1 D large₂ ∧ projection_sandwich_lattice D

def IntegralityFromMetric (C0 C' Cl Cg cb Cu cT CT : ℝ) (ca : AdmC) : Prop :=
  ca.Ok Cg → GamDef D large₂ ca.CE ca.CN → hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
    Adm1 D large₂ C0 C' Cl Cg cb Cu cT CT ca → Conclusion1 D large₂

def FamilyExpansionSecond (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → adm16 D large₂ C0 C' Cl Cg cb Cu cT CT → projection_sandwich_lattice D

def HodgeTateFromSandwich (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → adm16 D large₂ C0 C' Cl Cg cb Cu cT CT → Conclusion1 D large₂ → Conclusion2 D large₂ C0

def TowerRallisLemma (C0 C' Cl Cg cb Cu cT CT C : ℝ) (ca : AdmC) : Prop :=
  ca.Ok Cg → hyp D large₂ C0 C' Cl Cg cb Cu cT CT → adm10 D large₂ ca.n7 ca.A7 ca.C7 ca.cb7 ca.c7 → PointsLemma D large₂ C0 C

def Stmt (C0 C' Cl Cg cb Cu cT CT : ℝ) (ca : AdmC) : Prop :=
  ca.Ok Cg → GamDef D large₂ ca.CE ca.CN → hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
    admitted D large₂ C0 C' Cl Cg cb Cu cT CT ca → aux₃ D large₂

theorem statement_of_degree_and_bound {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} {ca : AdmC}
    (h1 : IntegralityFromMetric D large₂ C0 C' Cl Cg cb Cu cT CT ca) (h2 : FamilyExpansionSecond D large₂ C0 C' Cl Cg cb Cu cT CT) :
    Stmt D large₂ C0 C' Cl Cg cb Cu cT CT ca := by
  intro hOk hG hh hA
  exact ⟨h1 hOk hG hh hA.1, h2 hh hA.2.2⟩

end Conclusion₂

structure GivC where
  C0 : ℝ
  Cg : ℝ
  cb : ℝ
  Cu : ℝ
  cT : ℝ
  CT : ℝ

def GivC.Ok (gc : GivC) : Prop :=
  1 ≤ gc.C0 ∧ 0 < gc.Cg ∧ 0 < gc.cb ∧ 0 < gc.Cu ∧ 0 < gc.cT ∧ gc.cT ≤ gc.CT

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def AllR (P : ∀ D : D7, SizeData₂ D → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, P (Fm.D x i) (Fm.L x i)

def admF1 (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i => adm1 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT
def admF2 (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i => adm2 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT
def admF3 (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i => adm3 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT
def admF4 (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i => ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT
def admF5 (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i => adm5 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT
def admF6 (gc : GivC) (A c : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => adm6 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT A c
def admF7 (gc : GivC) (c C : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => adm7 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT c C
def admF8 (gc : GivC) (C : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => adm8 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT C
def admF9 (gc : GivC) (CA CA' Ce : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => adm9 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT CA CA' Ce
def FamilyRowsCountHypothesis (n0 : ℕ) (A C cb c : ℝ) : Prop := AllR Fm (fun D large₂ => adm10 D large₂ n0 A C cb c)
def FamilyWeylDimension (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i => WeylDimensionFormula (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT
def FamilyVandermondeLowerBound (gc : GivC) (ep0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => FilteredProjectionCriterion (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT ep0
def FamilyVandermondeUpperBound (gc : GivC) (C : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => VandermondeUpperBound (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT C
def FamilyWeylAndVandermonde (gc : GivC) (ep0 C : ℝ) : Prop := FamilyWeylDimension Fm gc ∧ FamilyVandermondeLowerBound Fm gc ep0 ∧ FamilyVandermondeUpperBound Fm gc C
def FamilyTwelfthHypothesis : Prop := adm12
def FamilyThirteenthHypothesis (gc : GivC) (C1 C2 c5 CA : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => adm13 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT C1 C2 c5 CA
def FamilyFourteenthHypothesis (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i => adm14 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT
def FamilyFifteenthHypothesis (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i => adm15 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT
def FamilySixteenthHypothesis (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i => adm16 (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT

def FirstFiltrationHypotheses (gc : GivC) (ca : AdmC) : Prop :=
  admF1 Fm gc ∧ admF2 Fm gc ∧ admF3 Fm gc ∧ admF4 Fm gc ∧ admF5 Fm gc ∧
    admF6 Fm gc ca.A5 ca.cL ∧ admF7 Fm gc ca.cN ca.CN ∧ admF8 Fm gc ca.CE ∧ admF9 Fm gc ca.CA ca.CA' ca.Ce ∧
    FamilyWeylAndVandermonde Fm gc ca.ep0 ca.CV ∧ FamilyTwelfthHypothesis ∧ FamilyThirteenthHypothesis Fm gc ca.C1 ca.C2 ca.c5 ca.CA ∧ FamilyFourteenthHypothesis Fm gc ∧ FamilyFifteenthHypothesis Fm gc

def AdmF (gc : GivC) (ca : AdmC) : Prop :=
  FirstFiltrationHypotheses Fm gc ca ∧ FamilyRowsCountHypothesis Fm ca.n7 ca.A7 ca.C7 ca.cb7 ca.c7 ∧ FamilySixteenthHypothesis Fm gc

def ConclusionF1 (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    hyp (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT → Conclusion1 (Fm.D x i) (Fm.L x i)

def FamilyBesselBoundFirstPart (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    hyp (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT → projection_sandwich_lattice (Fm.D x i)

def ConclusionF2 (gc : GivC) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    hyp (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT → Conclusion2 (Fm.D x i) (Fm.L x i) gc.C0

def ConclusionF3 (gc : GivC) (C : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    hyp (Fm.D x i) (Fm.L x i) gc.C0 C' Cl gc.Cg gc.cb gc.Cu gc.cT gc.CT → PointsLemma (Fm.D x i) (Fm.L x i) gc.C0 C

def OrbitValuationBound (gc : GivC) : Prop := ConclusionF1 Fm gc ∧ FamilyBesselBoundFirstPart Fm gc

def PeriodFamilyStatement (gc : GivC) (ca : AdmC) : Prop :=
  gc.Ok → ca.Ok gc.Cg → max ca.CE ca.CN + 1 ≤ Fm.CGam → FirstFiltrationHypotheses Fm gc ca → ConclusionF1 Fm gc

def FamilyUnfoldingCount (gc : GivC) : Prop := gc.Ok → FamilySixteenthHypothesis Fm gc → FamilyBesselBoundFirstPart Fm gc

def DeterminantValueFamily (gc : GivC) : Prop := gc.Ok → FamilySixteenthHypothesis Fm gc → ConclusionF1 Fm gc → ConclusionF2 Fm gc

def FlatLineDegreeFamilyStatement (gc : GivC) (ca : AdmC) (C : ℝ) : Prop :=
  gc.Ok → ca.Ok gc.Cg → FamilyRowsCountHypothesis Fm ca.n7 ca.A7 ca.C7 ca.cb7 ca.c7 → ConclusionF3 Fm gc C

def KudlaFamilyStatement (gc : GivC) (ca : AdmC) : Prop :=
  gc.Ok → ca.Ok gc.Cg → max ca.CE ca.CN + 1 ≤ Fm.CGam → AdmF Fm gc ca → OrbitValuationBound Fm gc

theorem family_statement_of_parts {Fm : Formalism.MainNotions.FamP eps} {gc : GivC} {ca : AdmC} (h1 : PeriodFamilyStatement Fm gc ca) (h2 : FamilyUnfoldingCount Fm gc) :
    KudlaFamilyStatement Fm gc ca := by
  intro hg hc hm hA
  exact ⟨h1 hg hc hm hA.1, h2 hg hA.2.2⟩

end Family

def ClosedFormWithDensityConstant (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ (gc : GivC) (ca : AdmC), Formalism.MainNotions.Closed 𝒞 fun Fm _ => PeriodFamilyStatement Fm gc ca

def LocalTopSecond (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ gc : GivC, Formalism.MainNotions.Closed 𝒞 fun Fm _ => FamilyUnfoldingCount Fm gc

def ClosedFirstSizeStatement (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ gc : GivC, Formalism.MainNotions.Closed 𝒞 fun Fm _ => DeterminantValueFamily Fm gc

def ClosedFamilyMomentFactorDefectBound (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ C : ℝ, ∀ (gc : GivC) (ca : AdmC), Formalism.MainNotions.Closed 𝒞 fun Fm _ => FlatLineDegreeFamilyStatement Fm gc ca C

def PropositionCStatement (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ (gc : GivC) (ca : AdmC), Formalism.MainNotions.Closed 𝒞 fun Fm _ => KudlaFamilyStatement Fm gc ca

theorem closed_form_of_parts {𝒞 : Formalism.MainNotions.FamClass} (h1 : ClosedFormWithDensityConstant 𝒞) (h2 : LocalTopSecond 𝒞) : PropositionCStatement 𝒞 := by
  intro gc ca
  exact Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and (h1 gc ca) (h2 gc)) fun _ _ _ h => family_statement_of_parts h.1 h.2

def ClosedFormConstantFunctions (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ (gc : List ℝ → GivC) (ca : List ℝ → AdmC),
    Formalism.MainNotions.Closed 𝒞 fun Fm _ => KudlaFamilyStatement Fm (gc Fm.cOut) (ca Fm.cOut)

theorem closed_form_of_functions {𝒞 : Formalism.MainNotions.FamClass} (h : ClosedFormConstantFunctions 𝒞) : PropositionCStatement 𝒞 := by
  intro gc ca
  exact h (fun _ => gc) (fun _ => ca)

end Formalism.MainNotions.AdmissibleBoundsFromSource
