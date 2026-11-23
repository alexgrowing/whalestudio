import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.DataKap
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace Formalism.MainNotions.InnerProductFormulaField

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Finset MeasureTheory
open Formalism.MainNotions.ZetaProductPairs (qE zetaProd idxPar Lpair)
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev Pl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

def normPl {D : D7} (v : Pl D) : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

def dLoc (q : ℝ) (t a : ℕ) : ℝ := zetaProd q (a + t) / zetaProd q t

structure Loc (D : D7) where

  Sg : Finset (Pl D)
  mem_Sg : ∀ v, v ∈ Sg ↔ ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal

  ZgCh : D.what₂.Tup → ℕ → D.what₂.FT → Pl D → ℂ
  ZgSb : D.what₂.Tup → ℕ → D.what₂.FT → Pl D → ℂ

  idxgCh : D.what₂.Tup → ℕ → Pl D → ℕ
  idxgSb : D.what₂.Tup → ℕ → Pl D → ℕ

  cCh : ℕ → ℝ
  cSb : ℕ → ℝ

  ZChR : ℕ → ℝ

  ZSbR : ℕ → ℝ

  nT : ℕ → ℝ

  massCh : ℕ → ℝ
  massSb : ℕ → ℝ
  mass_pos : ∀ j, 0 < massCh j ∧ 0 < massSb j

  LsS : D.what₂.Tup → ℕ → D.what₂.FT → ℂ

  LChS : D.what₂.Tup → ℕ → D.what₂.FT → ℂ

  Lfin : ℕ → ℕ → ℂ

  dFin : ℕ → ℂ

namespace Loc

variable {D : D7} (X : Loc D) (Z : DivX D)

def LmuS (μ : D.what₂.Tup) (i j : ℕ) : ℂ :=
  X.Lfin i j / ∏ v : Z.QPl μ, Lpair (Z.qv μ v) D.R.t (Z.nu μ v i / Z.nu μ v j)

def dS (μ : D.what₂.Tup) (a : ℕ) : ℂ :=
  X.dFin a / ((∏ v ∈ X.Sg, (dLoc (normPl v) D.R.t a : ℂ)) *
    ∏ v : Z.QPl μ, (dLoc (Z.qv μ v) D.R.t a : ℂ))

def volCh (μ : D.what₂.Tup) (j : ℕ) : ℝ :=
  X.massCh j * (∏ v ∈ X.Sg, (X.idxgCh μ j v : ℝ)) *
    ∏ v : Z.QPl μ, idxPar (Z.qv μ v) D.R.r (j * D.R.t)

def volSb (μ : D.what₂.Tup) (j : ℕ) : ℝ :=
  X.massSb j * (∏ v ∈ X.Sg, (X.idxgSb μ j v : ℝ)) * ∏ v : Z.QPl μ, idxPar (Z.qv μ v) D.R.r D.R.t

def sCh (μ : D.what₂.Tup) (j : ℕ) (π : D.what₂.FT) : ℂ :=
  X.cCh j * (X.LChS μ j π / X.dS Z μ (D.R.r + (j - 1) * D.R.t)) * X.ZChR j *
    ((∏ v ∈ X.Sg, X.ZgCh μ j π v) * ∏ v : Z.QPl μ, Z.ZQ μ v j) * X.volCh Z μ j

def lamR (μ : D.what₂.Tup) (j : ℕ) (π : D.what₂.FT) : ℂ :=
  X.cSb j * (X.LsS μ j π / X.dS Z μ D.R.r) * X.ZSbR j *
    ((∏ v ∈ X.Sg, X.ZgSb μ j π v) * ∏ v : Z.QPl μ, Z.quotientLocalValueFirst μ v) * X.volSb Z μ j

def ellgCh (μ : D.what₂.Tup) (j : ℕ) (π : D.what₂.FT) (v : Pl D) : ℂ :=
  (X.idxgCh μ j v : ℂ) * (zetaProd (normPl v) (D.R.r + j * D.R.t) : ℂ) * X.ZgCh μ j π v

def ellgSb (μ : D.what₂.Tup) (j : ℕ) (π : D.what₂.FT) (v : Pl D) : ℂ :=
  (X.idxgSb μ j v : ℂ) * (zetaProd (normPl v) (D.R.r + D.R.t) : ℂ) * X.ZgSb μ j π v

end Loc

def upChain (D : D7) (μ : D.what₂.Tup) : (i : ℕ) → D.what₂.EE →ₗ[ℂ] D.what₂.Mult μ i
  | 0 => (D.what₂.multZero μ).symm.toLinearEquiv.toLinearMap
  | i + 1 => (LinearMap.adjoint (D.what₂.io μ i)).comp (upChain D μ i)

def thBar {D : D7} (T : ThetaX D) (V W : HSp D) (χ χ' : T.Chr) (Φ : T.Sch V W) (F : T.cusp V) : T.AF W :=
  T.conjAF W (T.th V W χ χ' Φ ⟨T.conjAF V F, T.conjAF_cusp V F F.2⟩)

def IsTypeD {D : D7} (T : ThetaX D) (i : ℕ) (G : T.cusp (D.sp.Y i)) : Prop :=
  Formalism.MainNotions.ZetaProductPairs.IsTypeDv T i (G : T.AF (D.sp.Y i))

def thS {D : D7} (T : ThetaX D) (μ : D.what₂.Tup) (i : ℕ) (W : HSp D) (Φ : T.Sch (D.sp.Y i) W)
    (G : T.cusp (D.sp.Y i)) : T.AF W :=
  thBar T (D.sp.Y i) W (T.carY μ (i + 1) i) (T.carY μ (i + 1) (i + 1)) Φ G

def upAF {D : D7} (T : ThetaX D) (μ : D.what₂.Tup) (i : ℕ) (u : D.what₂.Mult μ i) : T.AF (D.sp.Y (i + 1)) :=
  (T.mY μ i : ℂ) • thS T μ i (D.sp.Y (i + 1)) (T.PhiYup μ i) (T.rowAF μ i u)

def ZAR (A : TH.ProvA) {p q r s : ℕ} (lam : Ix p q → ℚ) (Φ : Pol p q r s) (v : (A.ds p q lam).HK.V) : ℂ :=
  ∫ g, inner ℂ ((A.fock p q r s).ι Φ) ((A.fock p q r s).π (g, 1) ((A.fock p q r s).ι Φ)) *
    star (mcoef (A.ds p q lam) v g) ∂(A.grp p q).haar

def IsZ (A : TH.ProvA) {p q r s : ℕ} (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) (z : ℂ) : Prop :=
  ∃ (Φ : Pol p q r s) (v : (A.ds p q lam).HK.V),
    JointHW (A.fock p q r s) (blattner lam) (blattner lam') Φ ∧
    UnitHW (A.ds p q lam) (blattner lam) v ∧ z = ZAR A lam Φ v

def IsARZ (A : TH.ProvA) (z : ℂ) : Prop :=
  (∃ t al be ga de, Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧ IsZ A (lamA al be ga de) (lamA' t al be ga de) z) ∨
  (∃ t al be ga de, Formalism.MainNotions.SchurIrreducible.DataARm t al be ga de ∧ IsZ A (lamA al be ga de) (lamM' t al be ga de) z)

def logHk (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, Real.log (Real.Gamma (a i + n - i))) -
    ∑ i ∈ Finset.range n, ∑ l ∈ Finset.Ioo i n, Real.log (a i - a l + l - i)

def sumHkP (D : D7) (j : ℕ) : ℝ := ∑ τ, logHk (D.R.sigW j).1 (DV.aPlus D j τ)

def sumHkM (D : D7) (j : ℕ) : ℝ :=
  ∑ τ, logHk (D.R.sigW j).2 (fun i => DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i))

def sumHk (D : D7) (j : ℕ) : ℝ :=
  ∑ τ, (logHk (D.R.sigW j).1 (DV.aPlus D j τ) +
    logHk (D.R.sigW j).2 (fun i => DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i)))

def Lp (D : D7) (L : SizeData₂ D) : ℝ :=
  Real.log (L.sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

def TieRowTyp {D : D7} (T : ThetaX D) : Prop :=
  ∀ μ i, i ≤ D.R.m → ∀ x : D.what₂.Mult μ i,
    Formalism.MainNotions.ZetaProductPairs.IsTypeDv T i ((T.rowAF μ i x : T.cusp (D.sp.Y i)) : T.AF (D.sp.Y i))

def LamEig (D : D7) : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ π (c : ℂ), D.what₂.isot j π ≠ ⊥ →
    (∀ x ∈ D.what₂.isot j π, D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = c • x) →
    ((D.what₂.lamP μ j π : ℝ) : ℂ) = c

def ThB (D : D7) (κ : ℝ) : Prop :=
  ∀ (μ : D.what₂.Tup) (π : D.what₂.FT), ∀ x ∈ D.what₂.EEpart π,
    D.what₂.iota μ (D.what₂.thetaUp μ x) = ((κ * ∏ j ∈ Icc 1 D.R.m, D.what₂.lamP μ j π : ℝ) : ℂ) • x

def Nfun (D : D7) : ℕ := D.R.k + D.R.m * (D.R.t + (D.R.r + 6) + 1)

def GapHyp {D : D7} (T : ThetaX D) : Prop :=
  ∀ τ (j : ℕ) (h : j + 1 < D.R.m),
    2 * (Nfun D : ℝ) ^ 3 + D.R.t <
      ((((Formalism.MainNotions.ZetaProductPairs.parD T).b τ ⟨j + 1, h⟩ - (Formalism.MainNotions.ZetaProductPairs.parD T).b τ ⟨j, by omega⟩ : ℚ)) : ℝ)

theorem GapHyp_of_params {D : D7} (T : ThetaX D) {L : SizeData₂ D} (P : ParameterChoice' D L) : GapHyp T := by
  intro τ j h
  have h1 := (P.nodes_gap τ j h).1
  have h2 := P.heightBound_ge_rank_cubic
  have hb : (Formalism.MainNotions.ZetaProductPairs.parD T).b τ = (D.hc τ).b := D.hcW_b _ _
  rw [hb]
  have h3 : (Nfun D : ℝ) = (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1) := by
    unfold Nfun; push_cast; ring
  rw [h3]
  linarith

def Hyp (D : D7) (Z : DivX D) (T : ThetaX D) : Prop :=
  Formalism.MainNotions.ZetaProductPairs.WtHyp T ∧ TieRowTyp T ∧ LamEig D ∧ DV.KapRBase Z ∧ GapHyp T

variable (D : D7) (Z : DivX D) (T : ThetaX D) (A : TH.ProvA) (X : Loc D)

def adm1 : Prop :=
  (∀ j, 1 ≤ j → j ≤ D.R.m → 0 < X.cCh j ∧ 0 < X.cSb j) ∧
  (∀ (μ : D.what₂.Tup) (i : ℕ), i < D.R.m → ∀ π, ∀ x ∈ D.what₂.EEpart π, ∀ y ∈ D.what₂.EEpart π,
    ∀ Gx Gy : T.cusp (D.sp.Y (i + 1)),
      (Gx : T.AF (D.sp.Y (i + 1))) = upAF T μ i (upChain D μ i x) →
      (Gy : T.AF (D.sp.Y (i + 1))) = upAF T μ i (upChain D μ i y) →
      T.petY μ (i + 1) (Gx : T.AF (D.sp.Y (i + 1))) Gy =
        X.sCh Z μ (i + 1) π * inner ℂ (upChain D μ i x) (upChain D μ i y)) ∧
  (∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π, ∀ x ∈ D.what₂.isot j π, ∀ y ∈ D.what₂.isot j π,
    inner ℂ (D.what₂.thetaT μ j x) (D.what₂.thetaT μ j y) = X.lamR Z μ j π * inner ℂ x y)

def adm2 : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π,
    X.LChS μ j π = X.LsS μ j π * ∏ i ∈ Ico 1 j, X.LmuS Z μ i j

def adm3 : Prop :=
  Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A ∧
  (Formalism.MainNotions.ZetaProductPairs.WtHyp T →
    (∀ j, 1 ≤ j → j ≤ D.R.m →
      ∃ z : D.what₂.Tau → ℂ, (∀ τ, IsARZ A (z τ)) ∧ ((X.ZChR j : ℝ) : ℂ) = ∏ τ, z τ) ∧
    (∀ j, 1 ≤ j → j ≤ D.R.m → 0 < X.ZSbR j ∧ 0 < X.nT j) ∧
    (∀ (μ : D.what₂.Tup) (i l : ℕ), i < D.R.m → 1 ≤ l → l ≤ (sigYD D.R (i + 1)).2 →
      ∀ (Φ : T.Sch (D.sp.Y i) (T.YsLow D.R.t (i + 1) l)) (G : T.cusp (D.sp.Y i)), IsTypeD T i G →
        thS T μ i _ Φ G = 0))

def ArchimedeanSignatureMatching : Prop :=
  (∀ (μ : D.what₂.Tup) (i : ℕ), i < D.R.m →
    (∀ l, 1 ≤ l → l ≤ (sigYD D.R (i + 1)).2 →
      ∀ (Φ : T.Sch (D.sp.Y i) (T.YsLow D.R.t (i + 1) l)) (G : T.cusp (D.sp.Y i)), IsTypeD T i G →
        thS T μ i _ Φ G = 0) →
    ∀ (Φ : T.Sch (D.sp.Y i) (D.sp.Y (i + 1))) (G : T.cusp (D.sp.Y i)), IsTypeD T i G →
      thS T μ i _ Φ G ∈ T.cusp (D.sp.Y (i + 1))) ∧
  ∀ i j, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → i ≠ j → X.Lfin i j ≠ 0

def adm5 : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π, ∀ v ∈ X.Sg,
    X.ellgCh μ j π v = (zetaProd (normPl v) D.R.t : ℂ) ∧
      X.ellgSb μ j π v = (zetaProd (normPl v) D.R.t : ℂ)

def adm6 : Prop := Formalism.MainNotions.ZetaProductPairs.L2 Z

def adm7 : Prop :=
  (∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π, (X.LsS μ j π).im = 0 ∧ 0 < (X.LsS μ j π).re) ∧
  (∀ i j, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → i ≠ j →
    (X.Lfin i j).im = 0 ∧ 0 < (X.Lfin i j).re) ∧
  (∀ a, 1 ≤ a → (X.dFin a).im = 0 ∧ 0 < (X.dFin a).re)

def adm8 : Prop :=
  (∀ (μ : D.what₂.Tup) (π π' : D.what₂.FT), π ≠ π' → ∀ x ∈ D.what₂.EEpart π, ∀ y ∈ D.what₂.EEpart π',
    inner ℂ (D.what₂.thetaUp μ x) (D.what₂.thetaUp μ y) = 0) ∧
  (∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π π' : D.what₂.FT, π ≠ π' →
    ∀ x ∈ D.what₂.isot j π, ∀ y ∈ D.what₂.isot j π',
      inner ℂ x y = 0 ∧ inner ℂ (D.what₂.thetaT μ j x) (D.what₂.thetaT μ j y) = 0)

def adm9 : Prop :=
  ∀ (μ : D.what₂.Tup) (i : ℕ), i < D.R.m → ∀ (u u' : D.what₂.Mult μ i) (G G' : T.cusp (D.sp.Y (i + 1))),
    (G : T.AF (D.sp.Y (i + 1))) = upAF T μ i u → (G' : T.AF (D.sp.Y (i + 1))) = upAF T μ i u' →
    T.petY μ (i + 1) (G : T.AF (D.sp.Y (i + 1))) G' =
      (X.nT (i + 1) : ℂ) * inner ℂ (LinearMap.adjoint (D.what₂.io μ i) u) (LinearMap.adjoint (D.what₂.io μ i) u')

def adm10 : Prop := Formalism.MainNotions.PrimeDegreeVariant.ThetaUpInV0 D

def adm11 : Prop :=
  Rows.IsotInternal D.what₂ ∧ Rows.IsotRank D.what₂ ∧ ∀ π, 0 < D.what₂.nRows0 π

def admitted : Prop :=
  adm1 D Z T X ∧ adm2 D Z X ∧ adm3 D T A X ∧ ArchimedeanSignatureMatching D T X ∧ adm5 D X ∧ adm6 D Z ∧ adm7 D X ∧ adm8 D ∧
    adm9 D T X ∧ adm10 D ∧ adm11 D

def AdmLit : Prop := adm1 D Z T X ∧ adm2 D Z X ∧ ArchimedeanSignatureMatching D T X ∧ adm7 D X

def AdmOwn : Prop := adm8 D ∧ adm9 D T X

def admS (L : SizeData₂ D) (C : ℝ) : Prop :=
  (∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π,
    |Real.log (X.LsS μ j π).re - Real.log (X.dFin D.R.r).re| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 * Lp D L) ∧
  (∀ j, 1 ≤ j → j ≤ D.R.m → |Real.log (X.ZSbR j) - sumHk D j| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 * Lp D L) ∧
  (∀ j, 1 ≤ j → j ≤ D.R.m →
    |Real.log (X.cSb j * X.massSb j)| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 * Lp D L) ∧
  (∀ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ sumHkM D j)

def RallisScalarAction : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π,
    (∀ x ∈ D.what₂.isot j π, D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = X.lamR Z μ j π • x) ∧
    (X.lamR Z μ j π).im = 0 ∧ 0 < (X.lamR Z μ j π).re

def ConjugationNormInvariance : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π,
    (∀ x ∈ D.what₂.isot j π,
      D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = ((D.what₂.lamP μ j π : ℝ) : ℂ) • x) ∧
    (D.what₂.isot j π ≠ ⊥ →
      0 < D.what₂.lamP μ j π ∧ ((D.what₂.lamP μ j π : ℝ) : ℂ) = X.lamR Z μ j π)

def IsotypicPartsNonzero : Prop := ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ π, D.what₂.isot j π ≠ ⊥

def RallisSizeBound (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π, D.what₂.isot j π ≠ ⊥ →
    |Real.log (D.what₂.lamP μ j π) - sumHk D j| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 * Lp D L

def RallisLowerBound (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ π, D.what₂.isot j π ≠ ⊥ →
    sumHkP D j - C * D.R.f * (D.R.nV : ℝ) ^ 2 * Lp D L ≤ Real.log (D.what₂.lamP D.what₂.mu0 j π)

def LogEigenvalueLowerBound (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ π, D.what₂.isot j π ≠ ⊥ →
    sumHkP D j - C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La ≤ Real.log (D.what₂.lamP D.what₂.mu0 j π)

def Conclusion1 : Prop :=
  ∀ (μ : D.what₂.Tup) (π : D.what₂.FT),
    (∀ x ∈ D.what₂.EEpart π, ∀ i, i < D.R.m →
      upAF T μ i (upChain D μ i x) ∈ T.cusp (D.sp.Y (i + 1))) ∧
    ∃ La : ℝ, 0 < La ∧ ∀ x ∈ D.what₂.EEpart π, D.what₂.iota μ (D.what₂.thetaUp μ x) = (La : ℂ) • x

def ExactRallisProduct : Prop :=
  ∃ kap : ℝ, 0 < kap ∧ ∀ (μ : D.what₂.Tup) (π : D.what₂.FT), ∀ x ∈ D.what₂.EEpart π,
    D.what₂.iota μ (D.what₂.thetaUp μ x) = ((kap : ℂ) * ∏ j ∈ Icc 1 D.R.m, X.lamR Z μ j π) • x

def Conclusion2 : Prop := ThB D (Z.kapR D.what₂.embLL)

def iotaQ (D : D7) (μ : D.what₂.Tup) : D.what₂.Qsp μ →ₗ[ℂ] D.what₂.EE :=
  (D.what₂.iota μ).domRestrict (D.what₂.Qsp μ)

def PointsLemma : Prop :=
  ∀ μ : D.what₂.Tup, Function.Bijective (iotaQ D μ) ∧
    ∀ σ, (iotaQ D μ ∘ₗ LinearMap.adjoint (iotaQ D μ)) (D.what₂.onb σ) =
      ((Z.kapR D.what₂.embLL * ∏ j ∈ Icc 1 D.R.m, D.what₂.lamP μ j (D.what₂.ft σ) : ℝ) : ℂ) • D.what₂.onb σ

def aux₃ : Prop :=
  RallisScalarAction D Z X ∧ ConjugationNormInvariance D Z X ∧ IsotypicPartsNonzero D ∧ Conclusion1 D T ∧ ExactRallisProduct D Z X ∧ Conclusion2 D Z ∧ PointsLemma D Z

def Stmt : Prop := Hyp D Z T → admitted D Z T A X → aux₃ D Z T X

def SizesStatement (L : SizeData₂ D) (C K : ℝ) : Prop :=
  Hyp D Z T → admitted D Z T A X → 0 ≤ C → admS D X L C → RallisSizeBound D L (3 * C) ∧ RallisLowerBound D L (3 * C) ∧
    (0 ≤ Lp D L → Lp D L ≤ K * L.La → LogEigenvalueLowerBound D L (3 * C * K))

section RealConstant

variable {D} {T}

structure LocC (Y : Formalism.MainNotions.ZetaProductPairs.Loc D T) where

  Vc : D.what₂.Word → Type
  [acVc : ∀ u, AddCommGroup (Vc u)]
  [moVc : ∀ u, Module ℂ (Vc u)]

  VD : D.what₂.Word → Type
  [acVD : ∀ u, AddCommGroup (VD u)]
  [moVD : ∀ u, Module ℂ (VD u)]

  ell : ∀ u, Vc u →ₗ[ℂ] VD u →ₗ[ℂ] ℂ

  vOf : ∀ u, Y.ArchDat u → Vc u

  TOf : ∀ u, Y.ArchDat u → VD u

  ellT_eq : ∀ u da, Y.ellT u da = ell u (vOf u da) (TOf u da)

  v_free : ∀ u (v : Vc u) (da : Y.ArchDat u), ∃ da', vOf u da' = v ∧ TOf u da' = TOf u da

attribute [instance] LocC.acVc LocC.moVc LocC.acVD LocC.moVD

def Chain (T : ThetaX D) (P : TH.TPar D) (μ : ℕ → T.Chr) (π : Submodule ℂ (T.AF (T.Xs P.t 0)))
    (φ : T.AF (T.Xs P.t 0)) (F : ∀ j : ℕ, T.cusp (T.Ys P.t j))
    (Φ : ∀ j : ℕ, T.Sch (T.Ys P.t (j + 1)) (T.Ys P.t j)) : Prop :=
  Formalism.MainNotions.CayleySignature.IsMu T P μ ∧ Formalism.MainNotions.CayleySignature.IsAutRep T _ π ∧ π ≤ T.typeX P 0 ∧ φ ∈ π ∧
  Formalism.MainNotions.CayleySignature.IsDv T P D.R.m (F D.R.m : T.AF (T.Ys P.t D.R.m)) ∧
  (∀ j : ℕ, j < D.R.m → Φ j ∈ T.fact _ _ ∧ Φ j ∈ T.kfin _ _ ∧
    ((F j : T.cusp (T.Ys P.t j)) : T.AF (T.Ys P.t j)) = Formalism.MainNotions.CayleySignature.vth T P.t μ j (Φ j) (F (j + 1)) ∧
    Formalism.MainNotions.CayleySignature.IsDv T P j (F j : T.AF (T.Ys P.t j)))

def ParametersPolynomiallyBounded (T : ThetaX D) : Prop := ∀ u, Formalism.MainNotions.CayleySignature.Hyp3 T (T.parOf u)

def NonzeroBesselPeriodChain (D : D7) (T : ThetaX D) : Prop := Formalism.MainNotions.CayleySignature.PointsLemma D T

def UnfoldingAnyLevel (Y : Formalism.MainNotions.ZetaProductPairs.Loc D T) : Prop :=
  ∀ u,
    (∃ μ π φ F Φ, ∃ pos : T.Pos (T.Xs (T.parOf u).t 0) (T.Ys (T.parOf u).t 0) (T.iXYs (T.parOf u).t 0),
      Chain T (T.parOf u) μ π φ F Φ ∧ Formalism.MainNotions.CayleySignature.bB T (T.parOf u).t 0 pos 0 φ (F 0) ≠ 0) →
    ∃ μ π φ F Φ, ∃ pos : T.Pos (T.Xs (T.parOf u).t 0) (T.Ys (T.parOf u).t 0) (T.iXYs (T.parOf u).t 0),
      Chain T (T.parOf u) μ π φ F Φ ∧ Formalism.MainNotions.CayleySignature.bB T (T.parOf u).t 0 pos 0 φ (F 0) ≠ 0 ∧
      ∃ (n : ℕ) (Xp Yp : Fin n → ℂ) (dk : Fin n → Y.ArchDat u),
        Formalism.MainNotions.CayleySignature.bB T (T.parOf u).t 0 pos 0 φ (F 0) = ∑ k, Xp k * Y.ellT u (dk k) ∧
        ∀ k da, Y.ellT u da * Xp k = Y.Au u da * Yp k

def LinearFormNonzero {Y : Formalism.MainNotions.ZetaProductPairs.Loc D T} (W : LocC Y) : Prop := ∀ u, W.ell u ≠ 0

def ThetaOntoKFinite {Y : Formalism.MainNotions.ZetaProductPairs.Loc D T} (W : LocC Y) : Prop := ∀ u, Submodule.span ℂ (Set.range (W.TOf u)) = ⊤

def PeriodNonvanishingOnImage (Y : Formalism.MainNotions.ZetaProductPairs.Loc D T) : Prop := ∀ u, ∃ da, Y.ellT u da ≠ 0

theorem period_ne_zero_of_value {Y : Formalism.MainNotions.ZetaProductPairs.Loc D T} (W : LocC Y) (h : PeriodNonvanishingOnImage Y) : LinearFormNonzero W := by
  intro u h0
  obtain ⟨da, hda⟩ := h u
  apply hda
  rw [W.ellT_eq, h0]
  rfl

theorem value_ne_zero_of_onto {Y : Formalism.MainNotions.ZetaProductPairs.Loc D T} (W : LocC Y) (hE : LinearFormNonzero W) (hT : ThetaOntoKFinite W) : PeriodNonvanishingOnImage Y := by
  intro u
  by_contra hcon
  push Not at hcon
  refine hE u (LinearMap.ext fun v => ?_)
  refine LinearMap.ext_on (hT u) ?_
  rintro _ ⟨da, rfl⟩
  obtain ⟨da', h1, h2⟩ := W.v_free u v da
  have := hcon da'
  rw [W.ellT_eq, h1, h2] at this
  simpa using this

def RealConstantHypotheses {Y : Formalism.MainNotions.ZetaProductPairs.Loc D T} (_W : LocC Y) : Prop :=
  NonzeroBesselPeriodChain D T ∧ ParametersPolynomiallyBounded T ∧ UnfoldingAnyLevel Y

theorem term_of_unf {Y : Formalism.MainNotions.ZetaProductPairs.Loc D T} (h8 : NonzeroBesselPeriodChain D T) (hP : ParametersPolynomiallyBounded T) (hU : UnfoldingAnyLevel Y) (u : D.what₂.Word) :
    ∃ (Xp Yp : ℂ) (d0 : Y.ArchDat u), Xp ≠ 0 ∧ Y.ellT u d0 ≠ 0 ∧ ∀ da, Y.ellT u da * Xp = Y.Au u da * Yp := by
  obtain ⟨μ, π, φ, F, Φ, pos, h1, h2, h3, h4, h5, h6, hB⟩ := h8 (T.parOf u) (hP u)
  obtain ⟨μ', π', φ', F', Φ', pos', -, hB', n, Xp, Yp, dk, hs, hr⟩ :=
    hU u ⟨μ, π, φ, F, Φ, pos, ⟨h1, h2, h3, h4, h5, h6⟩, hB⟩
  rw [hs] at hB'
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hB'
  exact ⟨Xp k, Yp k, dk k, left_ne_zero_of_mul hk, right_ne_zero_of_mul hk, hr k⟩

theorem value_ne_zero_of_unfolding {Y : Formalism.MainNotions.ZetaProductPairs.Loc D T} (h8 : NonzeroBesselPeriodChain D T) (hP : ParametersPolynomiallyBounded T) (hU : UnfoldingAnyLevel Y) : PeriodNonvanishingOnImage Y := fun u =>
  let ⟨_, _, d0, _, h, _⟩ := term_of_unf h8 hP hU u
  ⟨d0, h⟩

end RealConstant

def ArchimedeanFactorNonvanishing (Y : Formalism.MainNotions.ZetaProductPairs.Loc D T) : Prop :=
  ∀ u, ∃ c : ℂ, c ≠ 0 ∧ (∀ da, Y.Au u da = c * Y.ellT u da) ∧ ∃ da, Y.ellT u da ≠ 0

def RealConstantStatement {D : D7} {T : ThetaX D} {Y : Formalism.MainNotions.ZetaProductPairs.Loc D T} (W : LocC Y) : Prop := RealConstantHypotheses W → ArchimedeanFactorNonvanishing D T Y

def IdentityWithHalfPowerFactor : Prop :=
  ∃ rho : D.what₂.Tup → ℝ, rho D.what₂.mu0 = 1 ∧
    (∀ μ, ∃ e : ℕ → ℤ, rho μ = ∏ p ∈ Z.Qp μ, (p : ℝ) ^ ((e p : ℝ) / 2)) ∧
    ∀ (μ : D.what₂.Tup) (π : D.what₂.FT), ∀ x ∈ D.what₂.EEpart π,
      D.what₂.iota μ (D.what₂.thetaUp μ x) =
        ((Z.kapR D.what₂.embLL * rho μ * ∏ j ∈ Icc 1 D.R.m, D.what₂.lamP μ j π : ℝ) : ℂ) • x

theorem half_power_of_exact_identity (h : Conclusion2 D Z) : IdentityWithHalfPowerFactor D Z := by
  refine ⟨fun _ => 1, rfl, fun μ => ⟨fun _ => 0, by simp⟩, fun μ π x hx => ?_⟩
  rw [h μ π x hx, mul_one]

def Loc.atLev {D : D7} (X : Loc D) (Zg : D.what₂.Tup → ℕ → D.what₂.FT → Pl D → ℂ)
    (idx : D.what₂.Tup → ℕ → Pl D → ℕ) : Loc D :=
  { X with ZgCh := Zg, idxgCh := idx }

structure LevObj {D : D7} (T : ThetaX D) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (S : RowSide D EE) where

  mY : D.what₂.Tup → ℕ → ℝ
  mY_pos : ∀ μ j, 0 < mY μ j

  rowAF : ∀ (μ : D.what₂.Tup) (j : ℕ), S.Mult μ j →ₗ[ℂ] T.cusp (D.sp.Y j)

  PhiYup : ∀ (_μ : D.what₂.Tup) (j : ℕ), T.Sch (D.sp.Y j) (D.sp.Y (j + 1))

  ZgCh : D.what₂.Tup → ℕ → D.what₂.FT → Pl D → ℂ

  idxgCh : D.what₂.Tup → ℕ → Pl D → ℕ

def LevObj.sharp {D : D7} (T : ThetaX D) (X : Loc D) : LevObj T (RowSide.sharp D) where
  mY := T.mY
  mY_pos := T.mY_pos
  rowAF := T.rowAF
  PhiYup := T.PhiYup
  ZgCh := X.ZgCh
  idxgCh := X.idxgCh

section Level

variable {D} {T} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]

def partL {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (π : D.what₂.FT) :
    Submodule ℂ EE := Submodule.span ℂ (b '' {σ | ty σ = π})

def upChainL (S : RowSide D EE) (μ : D.what₂.Tup) : (i : ℕ) → EE →ₗ[ℂ] S.Mult μ i
  | 0 => (S.multZero μ).symm.toLinearEquiv.toLinearMap
  | i + 1 => (LinearMap.adjoint (S.io μ i)).comp (upChainL S μ i)

def LevObj.upAF {S : RowSide D EE} (V : LevObj T S) (μ : D.what₂.Tup) (i : ℕ) (u : S.Mult μ i) :
    T.AF (D.sp.Y (i + 1)) :=
  (V.mY μ i : ℂ) • thS T μ i (D.sp.Y (i + 1)) (V.PhiYup μ i) (V.rowAF μ i u)

def LevObj.pet {S : RowSide D EE} (V : LevObj T S) (μ : D.what₂.Tup) (j : ℕ) (F : T.AF (D.sp.Y j)) (G : T.cusp (D.sp.Y j)) : ℂ :=
  (V.mY μ j : ℂ) * T.pet _ F G

def LevObj.loc {S : RowSide D EE} (V : LevObj T S) (X : Loc D) : Loc D := X.atLev V.ZgCh V.idxgCh

def TieRowTypL {S : RowSide D EE} (V : LevObj T S) : Prop :=
  ∀ μ i, i ≤ D.R.m → ∀ x : S.Mult μ i,
    Formalism.MainNotions.ZetaProductPairs.IsTypeDv T i ((V.rowAF μ i x : T.cusp (D.sp.Y i)) : T.AF (D.sp.Y i))

variable (S : RowSide D EE) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (V : LevObj T S)

def InnerProductAtLevel : Prop :=
  ∀ (μ : D.what₂.Tup) (i : ℕ), i < D.R.m → ∀ π, ∀ x ∈ partL b ty π, ∀ y ∈ partL b ty π,
    ∀ Gx Gy : T.cusp (D.sp.Y (i + 1)),
      (Gx : T.AF (D.sp.Y (i + 1))) = V.upAF μ i (upChainL S μ i x) →
      (Gy : T.AF (D.sp.Y (i + 1))) = V.upAF μ i (upChainL S μ i y) →
      V.pet μ (i + 1) (Gx : T.AF (D.sp.Y (i + 1))) Gy =
        (V.loc X).sCh Z μ (i + 1) π * inner ℂ (upChainL S μ i x) (upChainL S μ i y)

def LocalFactorAtLevel : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π, ∀ v ∈ X.Sg,
    (V.loc X).ellgCh μ j π v = (zetaProd (normPl v) D.R.t : ℂ)

def UpliftsOrthogonal : Prop :=
  ∀ (μ : D.what₂.Tup) (π π' : D.what₂.FT), π ≠ π' → ∀ x ∈ partL b ty π, ∀ y ∈ partL b ty π',
    inner ℂ (S.thetaUp μ x) (S.thetaUp μ y) = 0

def MultiplicityInnerProduct : Prop :=
  ∀ (μ : D.what₂.Tup) (i : ℕ), i < D.R.m → ∀ (u u' : S.Mult μ i) (G G' : T.cusp (D.sp.Y (i + 1))),
    (G : T.AF (D.sp.Y (i + 1))) = V.upAF μ i u → (G' : T.AF (D.sp.Y (i + 1))) = V.upAF μ i u' →
    V.pet μ (i + 1) (G : T.AF (D.sp.Y (i + 1))) G' =
      (X.nT (i + 1) : ℂ) * inner ℂ (LinearMap.adjoint (S.io μ i) u) (LinearMap.adjoint (S.io μ i) u')

def UpliftInV0AtLevel : Prop := Formalism.MainNotions.PrimeDegreeVariant.ThetaUpInV0Side S

def AdmL : Prop :=
  InnerProductAtLevel Z X S b ty V ∧ LocalFactorAtLevel X S V ∧ UpliftsOrthogonal S b ty ∧ MultiplicityInnerProduct X S V ∧ UpliftInV0AtLevel S

def TheoremBLocal : Prop :=
  ∀ (μ : D.what₂.Tup) (π : D.what₂.FT),
    (∀ x ∈ partL b ty π, ∀ i, i < D.R.m → V.upAF μ i (upChainL S μ i x) ∈ T.cusp (D.sp.Y (i + 1))) ∧
    ∃ La : ℝ, 0 < La ∧ ∀ x ∈ partL b ty π, S.iota μ (S.thetaUp μ x) = (La : ℂ) • x

def CorollaryALocal : Prop :=
  ∀ (μ : D.what₂.Tup) (π : D.what₂.FT), ∀ x ∈ partL b ty π,
    S.iota μ (S.thetaUp μ x) = ((S.kapOf ty * ∏ j ∈ Icc 1 D.R.m, D.what₂.lamP μ j π : ℝ) : ℂ) • x

def LevelIotaBijective : Prop :=
  ∀ μ : D.what₂.Tup, Function.Bijective (S.iotaQ μ) ∧
    ∀ σ, (S.iotaQ μ ∘ₗ LinearMap.adjoint (S.iotaQ μ)) (b σ) =
      ((S.kapOf ty * ∏ j ∈ Icc 1 D.R.m, D.what₂.lamP μ j (ty σ) : ℝ) : ℂ) • b σ

def ChainConstantLevelFree : Prop := 0 < n → 0 < D.what₂.Drows → S.kapOf ty = Z.kapR D.what₂.embLL

def ConclusionL : Prop := TheoremBLocal S b ty V ∧ CorollaryALocal S b ty ∧ LevelIotaBijective S b ty ∧ ChainConstantLevelFree Z S ty

def LiftingLemmasStatement : Prop :=
  Hyp D Z T → TieRowTypL V → admitted D Z T A X → AdmL Z X S b ty V → ConclusionL Z S b ty V

theorem lattice_clause_of_level_bijection (h : LevelIotaBijective S b ty) : S.RowLatticeBoundForBasis b ty (S.kapOf ty) := by
  refine ⟨fun μ => (h μ).1, S.kapOf_pos ty, fun _ => 1, rfl, fun _ => one_pos, DV.rhoUnit_one D, fun μ σ => ?_⟩
  rw [mul_one]
  exact (h μ).2 σ

end Level

structure LevDat {D : D7} (T : ThetaX D) where
  EE : Type
  [nacg : NormedAddCommGroup EE]
  [ips : InnerProductSpace ℂ EE]
  [fd : FiniteDimensional ℂ EE]
  S : RowSide D EE
  n : ℕ
  b : OrthonormalBasis (Fin n) ℂ EE
  ty : Fin n → D.what₂.FT
  V : LevObj T S

attribute [instance] LevDat.nacg LevDat.ips LevDat.fd

section Fam

variable {eps : ℝ}

abbrev LocF (Fm : Formalism.MainNotions.FamP eps) :=
  ∀ x (_hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i)

abbrev LevF (Fm : Formalism.MainNotions.FamP eps) :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LevDat (Fm.ex x hx i).th

def HypF (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Hyp (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).th

theorem GapHypF (Fm : Formalism.MainNotions.FamP eps) : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), GapHyp (Fm.ex x hx i).th :=
  fun x hx i => GapHyp_of_params _ (Fm.params x hx i)

def AdmF (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA) (XF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), admitted (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).th A (XF x hx i)

def OrbitValuationBound (Fm : Formalism.MainNotions.FamP eps) (XF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), aux₃ (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).th (XF x hx i)

def KudlaFamilyStatement (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA) (XF : LocF Fm) : Prop :=
  HypF Fm → AdmF Fm A XF → OrbitValuationBound Fm XF

def ExactStatementsFamily (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA) (XF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Stmt (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).th A (XF x hx i)

theorem family_of_pointwise_statements (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA) (XF : LocF Fm) (h : ExactStatementsFamily Fm A XF) : KudlaFamilyStatement Fm A XF :=
  fun hH hA x hx i => h x hx i (hH x hx i) (hA x hx i)

def FamilyLiftingStatement (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA) (XF : LocF Fm) (VF : LevF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    LiftingLemmasStatement (Fm.X x i) A (XF x hx i) (VF x hx i).S (VF x hx i).b (VF x hx i).ty (VF x hx i).V

def SizesFamily (C K : ℝ) (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA) (XF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    SizesStatement (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).th A (XF x hx i) (Fm.L x i) C K

abbrev LocCF (Fm : Formalism.MainNotions.FamP eps) (YF : Formalism.MainNotions.ZetaProductPairs.LocF Fm) :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocC (YF x hx i)

def RealConstantFamily (Fm : Formalism.MainNotions.FamP eps) (YF : Formalism.MainNotions.ZetaProductPairs.LocF Fm) (WF : LocCF Fm YF) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), RealConstantStatement (WF x hx i)

def heightComparisonConstant (Fm : Formalism.MainNotions.FamP eps) : ℝ := 2 * Fm.CYL + 2

end Fam

abbrev LocClass := ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps), TH.ProvA → LocF Fm → Prop

abbrev LocCClass := ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (YF : Formalism.MainNotions.ZetaProductPairs.LocF Fm), LocCF Fm YF → Prop

abbrev LevClass := ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps), LevF Fm → Prop

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) (𝒴 : LocClass) (𝒴' : LocCClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ A XF, 𝒴 Fm A XF → KudlaFamilyStatement Fm A XF) ∧
    Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ A XF, 𝒴 Fm A XF → ∀ C : ℝ, SizesFamily C (heightComparisonConstant Fm) Fm A XF) ∧
    Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ YF WF, 𝒴' Fm YF WF → RealConstantFamily Fm YF WF)

def ClosedLevelForms (𝒞 : Formalism.MainNotions.FamClass) (𝒴 : LocClass) (𝒱 : LevClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ A XF, 𝒴 Fm A XF → ExactStatementsFamily Fm A XF) ∧
    Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ A XF, 𝒴 Fm A XF → ∀ VF, 𝒱 Fm VF → FamilyLiftingStatement Fm A XF VF)

end Formalism.MainNotions.InnerProductFormulaField

end
