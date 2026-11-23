import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts

noncomputable section

namespace Formalism.MainNotions.WeightAlgebra

open Formalism.BasicNotions NumberField IsDedekindDomain

def wadd {D : D7} {j : ℕ} (w w' : WeightFamilies.Wt D j) : WeightFamilies.Wt D j where
  aP τ i := w.aP τ i + w'.aP τ i
  aM τ i := w.aM τ i + w'.aM τ i
  aPlus_antitone τ := (w.aPlus_antitone τ).add (w'.aPlus_antitone τ)
  aM_anti τ := (w.aM_anti τ).add (w'.aM_anti τ)
  n := w.n + w'.n
  n_even := w.n_even.add w'.n_even

def wsmul {D : D7} {j : ℕ} (c : ℕ) (w : WeightFamilies.Wt D j) : WeightFamilies.Wt D j where
  aP τ i := c * w.aP τ i
  aM τ i := c * w.aM τ i
  aPlus_antitone τ _ _ h := Nat.mul_le_mul_left c (w.aPlus_antitone τ h)
  aM_anti τ _ _ h := Nat.mul_le_mul_left c (w.aM_anti τ h)
  n := c * w.n
  n_even := w.n_even.mul_left c

def wscalar (D : D7) (j n : ℕ) (h : Even n) : WeightFamilies.Wt D j where
  aP _ _ := 0
  aM _ _ := 0
  aPlus_antitone _ _ _ _ := le_rfl
  aM_anti _ _ _ _ := le_rfl
  n := n
  n_even := h

def gapZ {p : ℕ} (l : Fin p → ℕ) (i : Fin p) : ℤ :=
  if h : i.1 + 1 < p then (l i : ℤ) - l ⟨i.1 + 1, h⟩ else l i

def absA {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) : ℝ := ∑ τ, ((∑ i, (w.aP τ i : ℝ)) + ∑ i, (w.aM τ i : ℝ))

def degP {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) : ℕ := ∑ τ, ((∑ i, w.aP τ i) + ∑ i, w.aM τ i)

def ncAt {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (τ : D.what₂.Tau) : ℤ :=
  (if h : 0 < (D.R.sigW j).1 then (w.aP τ ⟨(D.R.sigW j).1 - 1, by omega⟩ : ℤ) else 0) +
    (if h : 0 < (D.R.sigW j).2 then (w.aM τ ⟨(D.R.sigW j).2 - 1, by omega⟩ : ℤ) else 0) +
    w.n - ((D.R.sigW j).1 + (D.R.sigW j).2 : ℕ) + 1

def Tp (D : D7) (j T : ℕ) : ℕ := T + WeightFamilies.dimY D j + 2

def IsL (D : D7) {j : ℕ} (ka wL : WeightFamilies.Wt D j) (T nW : ℕ) : Prop :=
  wL.n = nW ∧
  (∀ τ i, gapZ (wL.aP τ) i = if i.1 + 1 < (D.R.sigW j).1
      then Int.fdiv (gapZ (ka.aP τ) i + 2) (Tp D j T)
      else Int.fdiv ((ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r) (Tp D j T)) ∧
  (∀ τ i, gapZ (wL.aM τ) i = if i.1 + 1 < (D.R.sigW j).2
      then Int.fdiv (gapZ (ka.aM τ) i + 2) (Tp D j T)
      else Int.fdiv (ka.aM τ i : ℤ) (Tp D j T))

def IsF' {D : D7} {j : ℕ} (ka wL wF : WeightFamilies.Wt D j) (T nP : ℕ) : Prop :=
  wF.n = nP ∧ (∀ τ i, (wF.aP τ i : ℤ) = ka.aP τ i - T * wL.aP τ i) ∧
    (∀ τ i, (wF.aM τ i : ℤ) = ka.aM τ i - T * wL.aM τ i)

def IsDoubledWeightWithShift {D : D7} {j : ℕ} (wL w1 : WeightFamilies.Wt D j) (nW : ℕ) : Prop :=
  w1.n + 2 = 2 * nW ∧ (∀ τ i, w1.aP τ i = 2 * wL.aP τ i) ∧ (∀ τ i, w1.aM τ i = 2 * wL.aM τ i)

def IsG2 {D : D7} {j : ℕ} (wL wF w2 : WeightFamilies.Wt D j) : Prop :=
  w2.n + wF.n = (WeightFamilies.dimY D j + 4) * wL.n ∧
  (∀ τ i, w2.aP τ i + wF.aP τ i = (WeightFamilies.dimY D j + 4) * wL.aP τ i) ∧
  (∀ τ i, w2.aM τ i + wF.aM τ i = (WeightFamilies.dimY D j + 4) * wL.aM τ i)

def resCh {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  ringChar (𝓞 K ⧸ la.asIdeal)

structure PJ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) where

  Forms : Type
  [rF : CommRing Forms]
  [aF : Algebra B.KO Forms]
  [aFO : Algebra (𝓞 B.KO) Forms]
  [stF : IsScalarTower (𝓞 B.KO) B.KO Forms]

  inc : ∀ w : WeightFamilies.Wt D j, B.Cusp j w →ₗ[B.KO] Forms
  inc_inj : ∀ w, Function.Injective (inc w)

  inc_indep : iSupIndep fun w => LinearMap.range (inc w)

  inc_mul : ∀ w w' (F : B.Cusp j w) (G : B.Cusp j w'), ∃ H : B.Cusp j (wadd w w'),
    inc w F * inc w' G = inc (wadd w w') H

  dat : P.Dat
  dat_rk : j < D.R.m → P.rk dat = D.R.r
  dat_jj : j < D.R.m → P.jj dat = (D.R.sigW j).1

  Pt : HeightOneSpectrum (𝓞 B.KO) → Type

  pt66 : ∀ la, Pt la → (P.loc dat (resCh la)).Pt (P.loc dat (resCh la)).YY

  vAt : ∀ la, Pt la → Forms → EReal
  vAt_zero : ∀ la y, vAt la y 0 = ⊤
  vAt_ne_bot : ∀ la y F, vAt la y F ≠ ⊥
  vAt_add : ∀ la y F G, min (vAt la y F) (vAt la y G) ≤ vAt la y (F + G)
  vAt_smul : ∀ la y (a : B.KO) F, a ≠ 0 →
    vAt la y (a • F) = (((vAdd la a : ℤ) : ℝ) : EReal) + vAt la y F

  vAt_mul : ∀ la y w w' (F : B.Cusp j w) (G : B.Cusp j w'),
    vAt la y (inc w F * inc w' G) = vAt la y (inc w F) + vAt la y (inc w' G)

  Mlat_eq : ∀ w (F : B.Cusp j w), F ∈ B.Mlat j w ↔ ∀ la (y : Pt la), 0 ≤ vAt la y (inc w F)

  thAll : ∀ w : WeightFamilies.Wt D j, Submodule (𝓞 B.KO) (B.Cusp j w)

  shortTh : ∀ w : WeightFamilies.Wt D j, Submodule (𝓞 B.KO) (B.Cusp j w)

attribute [instance] PJ.rF PJ.aF PJ.aFO PJ.stF

abbrev Prov (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Type 1 :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → PJ D B P j

structure Scal {D : D7} (B : WeightFamilies.Prov D) where
  sW : 𝓞 B.KO
  sF : 𝓞 B.KO
  s0 : 𝓞 B.KO
  sK : 𝓞 B.KO

namespace PJ

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)

def phiC (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) : ℝ :=
  open Classical in
  if j < D.R.m then (eWL B.KO la : ℝ) * (P.loc X.dat (resCh la)).phiCy (X.pt66 la y) else 0

def emb (w : WeightFamilies.Wt D j) (N : Submodule (𝓞 B.KO) (B.Cusp j w)) : Submodule (𝓞 B.KO) X.Forms :=
  N.map ((X.inc w).restrictScalars (𝓞 B.KO))

def scaled (_X : PJ D B P j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) (N : Submodule (𝓞 B.KO) (B.Cusp j w)) :
    Submodule (𝓞 B.KO) (B.Cusp j w) :=
  N.map (s • (LinearMap.id : B.Cusp j w →ₗ[𝓞 B.KO] B.Cusp j w))

def Msup (w : WeightFamilies.Wt D j) : Submodule (𝓞 B.KO) X.Forms := X.emb w (B.Mlat j w)

def WWc (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) : Submodule (𝓞 B.KO) (B.Cusp j w) := X.scaled s w (X.thAll w)

def Thc (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) : Submodule (𝓞 B.KO) (B.Cusp j w) :=
  X.scaled s w ((X.shortTh w).map
    ((((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n)) • LinearMap.id))

def depth (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) : EReal :=
  ⨅ F ∈ X.WWc s w, X.vAt la y (X.inc w F)

def wF0 (_X : PJ D B P j) (wL wF : WeightFamilies.Wt D j) : WeightFamilies.Wt D j := wadd wF (wsmul (WeightFamilies.dimY D j) wL)

def Theta (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : Submodule (𝓞 B.KO) X.Forms :=
  X.emb wL (X.WWc S.sW wL) ^ T * X.emb wF (X.Thc S.sF wF) ⊔
    X.emb wL (X.WWc S.sW wL) ^ (T - WeightFamilies.dimY D j) * X.emb (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF)) ⊔
    X.emb ka (X.Thc S.sK ka)

def rk (_X : PJ D B P j) (w : WeightFamilies.Wt D j) (N : Submodule (𝓞 B.KO) (B.Cusp j w)) : ℕ :=
  Module.finrank B.KO (Submodule.span B.KO (N : Set (B.Cusp j w)))

def lN (_X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) : ℝ := lw B.KO la

abbrev Kl (_X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) := la.adicCompletion B.KO

abbrev Ol (_X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) := la.adicCompletionIntegers B.KO

abbrev Vl (la : HeightOneSpectrum (𝓞 B.KO)) := TensorProduct B.KO (X.Kl la) X.Forms

def bc (la : HeightOneSpectrum (𝓞 B.KO)) : X.Forms →ₗ[B.KO] X.Vl la :=
  TensorProduct.mk B.KO (X.Kl la) X.Forms 1

def loc (la : HeightOneSpectrum (𝓞 B.KO)) (N : Submodule (𝓞 B.KO) X.Forms) :
    Submodule (X.Ol la) (X.Vl la) :=
  Submodule.span (X.Ol la) (X.bc la '' (N : Set X.Forms))

def locK (la : HeightOneSpectrum (𝓞 B.KO)) (N : Submodule (𝓞 B.KO) X.Forms) :
    Submodule (X.Kl la) (X.Vl la) :=
  Submodule.span (X.Kl la) (X.bc la '' (N : Set X.Forms))

def ofK (la : HeightOneSpectrum (𝓞 B.KO)) (V : Submodule (X.Kl la) (X.Vl la)) :
    Submodule (X.Ol la) (X.Vl la) := V.restrictScalars (X.Ol la)

def qlen (la : HeightOneSpectrum (𝓞 B.KO)) (A A' : Submodule (X.Ol la) (X.Vl la)) : ℕ∞ :=
  Module.length (X.Ol la) (A ⧸ A'.comap A.subtype)

def bad (_X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  (((2 * (NumberField.discr D.host.E).natAbs * D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ∈ la.asIdeal)

open Classical in

def eLa (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (la : HeightOneSpectrum (𝓞 B.KO)) : ℤ :=
  ⌈(T : ℝ) * (nus la + if X.bad la then 1 else 0)⌉

def NonZeroComp (w : WeightFamilies.Wt D j) (F : B.Cusp j w) : Prop :=
  ∀ w' (G : B.Cusp j w'), X.inc w F * X.inc w' G = 0 → G = 0

end PJ

def qq (D : D7) : ℕ := min (D.host.g 0) (D.host.g 1)

def g0 (D : D7) : ℕ := 2 * 5 ^ 4 * D.R.r

def DF {D : D7} {j : ℕ} (wL : WeightFamilies.Wt D j) : ℕ := degP wL

def cc (D : D7) (large₂ : SizeData₂ D) {j : ℕ} (Cc Ac CRc : ℝ) (wL : WeightFamilies.Wt D j) : ℝ :=
  WeightFamilies.RRv D CRc * WeightFamilies.PPv D large₂ Cc Ac * (DF wL : ℝ) ^ 2 / (qq D : ℝ)

structure KHyp where
  CK : ℝ
  CA : ℝ
  C1 : ℝ
  A1 : ℝ
  Cc : ℝ
  Ac : ℝ
  CRc : ℝ

structure KAdm where
  CG : ℝ
  AG : ℝ
  Cf : ℝ
  Af : ℝ
  CW : ℝ
  AW : ℝ
  CL : ℝ
  AL : ℝ
  CRm : ℝ

structure DHyp where
  A1 : ℝ
  Ac : ℝ
  CRc : ℝ

structure DAdm where
  AG : ℝ
  Af : ℝ
  AW : ℝ
  AL : ℝ
  CRm : ℝ

def KHyp.deg (H : KHyp) : DHyp := ⟨H.A1, H.Ac, H.CRc⟩

def KAdm.deg (K : KAdm) : DAdm := ⟨K.AG, K.Af, K.AW, K.AL, K.CRm⟩

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

def ParA (large₂ : SizeData₂ D) (CA : ℝ) : Prop :=
  large₂.sc.x ≤ (D.R.f : ℝ) * D.R.r ∧ (D.R.f : ℝ) * D.R.r ≤ large₂.sc.x ^ CA ∧
  Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| ≤ CA * ((D.R.f : ℝ) * D.R.r * large₂.sc.L) ∧
  large₂.sc.x ^ (-large₂.sc.eps) ≤ large₂.de2 ∧
  (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧
  |large₂.logDerivativeAtOne| ≤ large₂.sc.x ^ large₂.sc.eps ∧ |large₂.logOm| ≤ CA * large₂.sc.L ∧
  Real.log D.host.pde ≤ large₂.sc.L ∧ Real.log D.host.pde' ≤ large₂.sc.L ∧
  2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE

def lamStar (D : D7) : ℝ :=
  Real.log ((D.host.g 0 : ℝ) * D.host.g 1) + Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)

def PN (D : D7) (large₂ : SizeData₂ D) : ℝ := 2 * large₂.sc.L + lamStar D + 4

def n0 (D : D7) (j : ℕ) : ℕ := D.R.r + 2 * g0 D * (D.R.f * (D.R.sigW j).1 * (D.R.sigW j).2 + 1)

def Zb (D : D7) (large₂ : SizeData₂ D) : ℝ := (D.R.f : ℝ) * D.R.r * large₂.sc.L

def lrd (D : D7) : ℝ := Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| / (2 * D.R.f)

def PU (D : D7) : ℝ := (D.R.f : ℝ) * D.R.r * (2 * lrd D + 2 * Real.log ((D.R.f : ℝ) * D.R.r) + 3)

def PO (D : D7) (large₂ : SizeData₂ D) : ℝ := 19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * large₂.sc.L + 198 * (D.R.f : ℝ) ^ 2 * large₂.sc.L

def sizeConstantAtParamsWeight (D : D7) (nW : ℕ) : ℝ :=
  max (90 * ((D.R.f : ℝ) * D.R.r + 1)) (max (360 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3)
    (max (2 * (3 * (D.R.r : ℝ) + 3 + D.R.r * Real.log D.R.r)) (max (nW : ℝ) (max (g0 D : ℝ)
      (max ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 + 6) 11)))))

def DivisibilityWeightConstant (D : D7) (j : ℕ) : ℝ :=
  72 * 5 ^ 4 * (WeightFamilies.dimY D j : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 * (D.R.m : ℝ) ^ 4

def DomAt (D : D7) (large₂ : SizeData₂ D) (j nW : ℕ) (CP : ℝ) : Prop :=
  1000 ≤ CP ∧ CP ^ 20 ≤ Zb D large₂ ∧
    lamStar D ≤ CP * Zb D large₂ ∧ PN D large₂ ≤ CP * Zb D large₂ ∧
    Real.log ((D.host.condN : ℝ) * D.host.g 0 * D.host.g 1) ≤ CP * Zb D large₂ ∧ PU D ≤ CP * Zb D large₂ ∧
    PO D large₂ ≤ CP * Zb D large₂ ^ 2 ∧ (n0 D j : ℝ) ≤ CP * Zb D large₂ ^ 3 ∧ sizeConstantAtParamsWeight D nW ≤ CP * Zb D large₂ ^ 4 ∧
    DivisibilityWeightConstant D j ≤ CP * Zb D large₂ ^ 10

def DomHyp (D : D7) (large₂ : SizeData₂ D) (j nW : ℕ) : Prop := ∃ CP : ℝ, DomAt D large₂ j nW CP

theorem DomAt.domHyp {D : D7} {large₂ : SizeData₂ D} {j nW : ℕ} {CP : ℝ} (h : DomAt D large₂ j nW CP) : DomHyp D large₂ j nW := ⟨CP, h⟩

theorem DomAt.mono {D : D7} {large₂ : SizeData₂ D} {j nW : ℕ} {CP C2 : ℝ} (h : DomAt D large₂ j nW CP) (hle : CP ≤ C2)
    (hZ : C2 ^ 20 ≤ Zb D large₂) : DomAt D large₂ j nW C2 := by
  obtain ⟨h1, -, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hC2 : 0 ≤ C2 := by linarith
  have hZ0 : 0 ≤ Zb D large₂ := le_trans (pow_nonneg hC2 20) hZ
  refine ⟨by linarith, hZ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h3.trans (mul_le_mul_of_nonneg_right hle hZ0)
  · exact h4.trans (mul_le_mul_of_nonneg_right hle hZ0)
  · exact h5.trans (mul_le_mul_of_nonneg_right hle hZ0)
  · exact h6.trans (mul_le_mul_of_nonneg_right hle hZ0)
  · exact h7.trans (mul_le_mul_of_nonneg_right hle (pow_nonneg hZ0 2))
  · exact h8.trans (mul_le_mul_of_nonneg_right hle (pow_nonneg hZ0 3))
  · exact h9.trans (mul_le_mul_of_nonneg_right hle (pow_nonneg hZ0 4))
  · exact h10.trans (mul_le_mul_of_nonneg_right hle (pow_nonneg hZ0 10))

def OPO (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) : Prop :=
  Real.log (Module.finrank ℚ B.KO) ≤ PO D large₂ ∧
  Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO ≤ PO D large₂

def PI4 (D : D7) (j : ℕ) (PLam lNc : ℝ) : ℝ := 5 * (PLam + lamStar D) + 2 * lNc / (WeightFamilies.dimY D j : ℝ)

def Gc (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (PLam : ℝ) (po : ℕ) : ℝ :=
  PLam + (3 * large₂.sc.L + 2 * max
      (Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO)
      (Real.log (Module.finrank ℚ D.host.E) + Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| / Module.finrank ℚ D.host.E)) +
    2 * (D.R.f : ℝ) * D.R.r * (lamStar D + 2 * Real.log po) + 31 * Zb D large₂

section J

variable {j : ℕ}

def ShortG (_X : PJ D B P j) (w : WeightFamilies.Wt D j) (N : Submodule (𝓞 B.KO) (B.Cusp j w)) (β : ℝ) : Prop :=
  ∃ Sh : Finset (B.Cusp j w), (Sh : Set (B.Cusp j w)) ⊆ N ∧
    Submodule.span B.KO (Sh : Set (B.Cusp j w)) = ⊤ ∧ ∀ g ∈ Sh, WeightFamilies.meanLogSup B g ≤ β

def S4 (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (G : ℝ) : Prop :=
  (∃ Sh : Finset (B.Cusp j wL), Submodule.span (𝓞 B.KO) (Sh : Set (B.Cusp j wL)) = X.WWc S.sW wL ∧
    ∃ mx : (B.KO →+* ℂ) → ℝ, (∀ σ, ∀ g ∈ Sh, Real.log (B.supN j wL σ g) ≤ mx σ) ∧
      (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size) ∧
  ShortG X wF (X.Thc S.sF wF) (G * wF.size) ∧
  ShortG X (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF)) (G * (X.wF0 wL wF).size) ∧
  ShortG X ka (X.Thc S.sK ka) (G * ka.size)

def SetC (large₂ : SizeData₂ D) (_X : PJ D B P j) (CK C1 _A1 : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ)
    (h0 : ℝ) : Prop :=
  ka.n = D.R.nV ∧
  (∀ τ i, i.1 + 1 < (D.R.sigW j).1 →
    ((Tp D j T * (Tp D j T + 2 * D.R.r) : ℕ) : ℤ) ≤ gapZ (ka.aP τ) i + 2) ∧
  (∀ τ i, i.1 + 1 < (D.R.sigW j).2 →
    ((Tp D j T * (Tp D j T + 2 * D.R.r) : ℕ) : ℤ) ≤ gapZ (ka.aM τ) i + 2) ∧
  4 * (T : ℝ) ^ 2 + D.R.t + 1 ≤ h0 ∧
  (∀ τ, h0 / 4 - D.R.t ≤ (ncAt ka τ : ℝ)) ∧
  (∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
    h0 / 2 - ((D.R.t : ℝ) + 1) / 2 ≤ (ka.aP τ i : ℝ)) ∧
  (∀ τ (i : Fin (D.R.sigW j).2), i.1 + 1 = (D.R.sigW j).2 →
    h0 / 2 - ((D.R.t : ℝ) + 1) / 2 ≤ (ka.aM τ i : ℝ)) ∧
  ka.size ≤ CK * D.R.k * D.R.f * large₂.sc.b ∧
  Even nP ∧ 8 * D.R.f * D.R.r + 4 ≤ nP ∧ nP ≤ nW ∧ (nW : ℝ) ≤ sizeConstantAtParamsWeight D nW ∧
  D.R.f * D.R.r * (D.R.r + 1) ≤ nW ∧ D.R.nV = nP + T * nW ∧
  IsL D ka wL T nW ∧ IsF' ka wL wF T nP ∧
  wL.size ≤ CK * D.R.k * D.R.f * large₂.sc.b / T ∧
  0 < T ∧ WeightFamilies.dimY D j ≤ T ∧ 40 * (WeightFamilies.dimY D j + 2) ≤ T ∧
  (WeightFamilies.dimY D j + 2) * nW + 2 * D.R.r ≤ T ∧
  40 ≤ nW ∧ n0 D j ≤ T ∧ 11 * WeightFamilies.dimY D j ^ 2 ≤ T ∧
  OPO large₂ B ∧
  DomAt D large₂ j nW C1

def ScalB (large₂ : SizeData₂ D) (X : PJ D B P j) (_C1 _A1 : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (_T : ℕ) : Prop :=
  S.sW ≠ 0 ∧ S.sF ≠ 0 ∧ S.s0 ≠ 0 ∧ S.sK ≠ 0 ∧
  (∀ σ : B.KO →+* ℂ, 0 ≤ Real.log ‖σ (S.sW : B.KO)‖ ∧
    (DF wL : ℝ) / 2 * Real.log (qq D) ≤ Real.log ‖σ (S.sW : B.KO)‖) ∧
  ∃ po ∈ ({D.host.pde, D.host.pde'} : Set ℕ),
    (∀ σ : B.KO →+* ℂ,
      Real.log ‖σ (S.sW : B.KO)‖ ≤ (lamStar D + 2 * Real.log po) * wL.size ∧
      Real.log ‖σ (S.sF : B.KO)‖ ≤ (lamStar D + 2 * Real.log po) * wF.size ∧
      Real.log ‖σ (S.s0 : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log po) * (X.wF0 wL wF).size ∧
      Real.log ‖σ (S.sK : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log po) * ka.size) ∧
    ∃ PLam : ℝ, PLam ≤ 1009 * Zb D large₂ ∧ S4 X S ka wL wF (Gc large₂ B PLam po)

theorem ScalB.lower {large₂ : SizeData₂ D} {X : PJ D B P j} {C1 A1 : ℝ} {S : Scal B} {ka wL wF : WeightFamilies.Wt D j} {T : ℕ}
    (h : ScalB large₂ X C1 A1 S ka wL wF T) (hq : 0 < qq D) (σ : B.KO →+* ℂ) :
    1 ≤ ‖σ (S.sW : B.KO)‖ ∧ (qq D : ℝ) ^ ((DF wL : ℝ) / 2) ≤ ‖σ (S.sW : B.KO)‖ := by
  obtain ⟨hW, -, -, -, hl, -⟩ := h
  obtain ⟨h1, h2⟩ := hl σ
  have hne : (S.sW : B.KO) ≠ 0 := by exact_mod_cast hW
  have hpos : 0 < ‖σ (S.sW : B.KO)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hne)
  refine ⟨?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have := Real.log_neg hpos hc
    linarith
  · have hq' : (0 : ℝ) < (qq D : ℝ) := by exact_mod_cast hq
    rw [Real.rpow_def_of_pos hq']
    calc Real.exp (Real.log (qq D : ℝ) * ((DF wL : ℝ) / 2))
        ≤ Real.exp (Real.log ‖σ (S.sW : B.KO)‖) := by
          apply Real.exp_le_exp.mpr
          rw [mul_comm]
          exact h2
      _ = ‖σ (S.sW : B.KO)‖ := Real.exp_log hpos

def H1 (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (S : Scal B) (wL : WeightFamilies.Wt D j)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  (∀ la, 0 ≤ nus la) ∧ (Function.support nus).Finite ∧
  (∑ᶠ la, |nus la| * X.lN la) ≤ PN D large₂ * wL.size ∧
  ∀ la (y : X.Pt la), X.depth S.sW wL la y ≤
    ((nus la + cc D large₂ H.Cc H.Ac H.CRc wL * X.phiC la y : ℝ) : EReal)

def H2 (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) : Prop :=
  X.WWc S.sW wL ≤ B.Mlat j wL ∧ X.Thc S.sF wF ≤ B.Mlat j wF ∧
  X.Thc S.s0 (X.wF0 wL wF) ≤ B.Mlat j (X.wF0 wL wF) ∧ X.Thc S.sK ka ≤ B.Mlat j ka

def H3 (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR Bx : ℝ) (wL : WeightFamilies.Wt D j) (T : ℕ) : Prop :=
  large₂.sc.x ^ Bx * WeightFamilies.RRv D CR ^ 4 * WeightFamilies.PPv D large₂ C2 A2 ^ 3 * (DF wL : ℝ) ^ 2 ≤ qq D ∧
  large₂.sc.x ^ Bx * T * g0 D * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2 ≤ qq D ∧
  large₂.sc.x ^ Bx * WeightFamilies.PPv D large₂ C2 A2 ^ 4 * (WeightFamilies.dimY D j : ℝ) ^ 3 * D.R.k * D.R.f / (D.R.m * large₂.de2) ≤ T ∧
  (T : ℝ) * cc D large₂ H.Cc H.Ac H.CRc wL * g0 D ≤ 1 ∧
  (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * WeightFamilies.RRv D CR ^ 2 * cc D large₂ H.Cc H.Ac H.CRc wL ≤ 1 / 2 ∧
  ((WeightFamilies.dimY D j + 4) * DF wL : ℝ) ≤ (qq D : ℝ) - 2

def H4 (large₂ : SizeData₂ D) (X : PJ D B P j) (_H : KHyp) (C2 A2 CR : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nW : ℕ) : Prop :=
  large₂.sc.b ≤ ka.size ∧ (T : ℝ) * wL.size ≤ 2 * ka.size ∧
  wF.size ≤ ((WeightFamilies.dimY D j : ℝ) + 2) * wL.size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T ∧
  WeightFamilies.PPv D large₂ C2 A2 ^ 3 * (T : ℝ) ^ 2 ≤ large₂.sc.b ∧
  WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ≤ large₂.sc.b ∧
  (∀ i, 2 * DF ka + 2 < D.host.g i) ∧
  ∃ PLam lNc : ℝ, PLam ≤ 1009 * Zb D large₂ ∧ lNc ≤ 81 * Zb D large₂ ^ 2 ∧
  (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th ∈ B.Mlat j w1, X.NonZeroComp w1 th ∧
    ∀ σ, Real.log (B.supN j w1 σ th) ≤ 2 * PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size) ∧
  ∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 ∧ ∃ th ∈ B.Mlat j w2, X.NonZeroComp w2 th ∧
    ∀ σ, Real.log (B.supN j w2 σ th) ≤ PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size

def Concl (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) : Prop :=
  ∃ r : HeightOneSpectrum (𝓞 B.KO) → ℝ, (∀ la, 0 ≤ r la) ∧
    Summable (fun la => r la * X.lN la) ∧ (∑' la, r la * X.lN la) ≤ β ∧
    ∀ la (e : ℤ), (T : ℝ) * nus la ≤ e →
    ∀ V' : Submodule (X.Kl la) (X.Vl la), V' ≤ X.locK la (X.Msup ka) →
      X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
        (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
          (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
        (e : ℝ) * (Module.finrank (X.Kl la) V' : ℝ) + r la

theorem Concl.at_eLa {X : PJ D B P j} {S : Scal B} {ka wL wF : WeightFamilies.Wt D j} {T : ℕ}
    {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} {β : ℝ} (h : Concl X S ka wL wF T nus β) :
    ∃ r : HeightOneSpectrum (𝓞 B.KO) → ℝ, (∀ la, 0 ≤ r la) ∧
    Summable (fun la => r la * X.lN la) ∧ (∑' la, r la * X.lN la) ≤ β ∧
    ∀ la (V' : Submodule (X.Kl la) (X.Vl la)), V' ≤ X.locK la (X.Msup ka) →
      X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
        (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
          (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
        (X.eLa T nus la : ℝ) * (Module.finrank (X.Kl la) V' : ℝ) + r la := by
  obtain ⟨r, hr0, hrs, hrb, hr⟩ := h
  refine ⟨r, hr0, hrs, hrb, fun la V' hV' => hr la (X.eLa T nus la) ?_ V' hV'⟩
  unfold PJ.eLa
  refine le_trans ?_ (Int.le_ceil _)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg T)
  split_ifs <;> linarith

def Hyp (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  ParA large₂ H.CA ∧ SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0 ∧ ScalB large₂ X H.C1 H.A1 S ka wL wF T ∧
    H1 large₂ X H S wL nus ∧ H2 X S ka wL wF ∧ H3 large₂ H C2 A2 CR Bx wL T ∧
    H4 large₂ X H C2 A2 CR ka wL wF T nW ∧ (T : ℝ) ≤ large₂.sc.x ^ CT

end J

theorem dP_sq_le {large₂ : SizeData₂ D} {CA CRm : ℝ} (h : ParA large₂ CA) (hC : 2 ≤ CRm) (j : ℕ) :
    ((WeightFamilies.dP D j : ℕ) : ℝ) ^ 2 ≤ WeightFamilies.RRv D CRm := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hm⟩ := h
  have hn : WeightFamilies.dP D j ≤ 2 * D.R.f * D.R.m := by
    unfold WeightFamilies.dP WeightFamilies.rho
    exact Nat.mul_le_mul le_rfl (Nat.sub_le D.R.m j)
  have hcast : ((WeightFamilies.dP D j : ℕ) : ℝ) ≤ 2 * (D.R.f : ℝ) * D.R.m := by exact_mod_cast hn
  have hle : ((WeightFamilies.dP D j : ℕ) : ℝ) ≤ D.host.rdE := hcast.trans hm
  have h0r : (0 : ℝ) ≤ D.host.rdE := (Nat.cast_nonneg _).trans hle
  unfold WeightFamilies.RRv
  rcases Nat.eq_zero_or_pos (WeightFamilies.dP D j) with h0 | hpos
  · rw [h0]
    calc ((0 : ℕ) : ℝ) ^ 2 = 0 := by simp
      _ ≤ D.host.rdE ^ CRm := Real.rpow_nonneg h0r _
  · have h1 : (1 : ℝ) ≤ D.host.rdE := le_trans (by exact_mod_cast hpos) hle
    calc ((WeightFamilies.dP D j : ℕ) : ℝ) ^ 2 ≤ D.host.rdE ^ 2 := by gcongr
      _ = D.host.rdE ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ ≤ D.host.rdE ^ CRm := Real.rpow_le_rpow_of_exponent_le h1 hC

def Conclusion1 (large₂ : SizeData₂ D) (X : Prov D B P) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    Hyp large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

def Conclusion2 (large₂ : SizeData₂ D) (X : Prov D B P) (H : KHyp) (C2 A2 CR Bx CT A : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    Hyp large₂ (X j h1 h2) H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.m * large₂.sc.b * large₂.sc.x ^ (-A))

def adm1 (B : WeightFamilies.Prov D) : Prop := WeightFamilies.adm1 B

def adm2 (large₂ : SizeData₂ D) (X : Prov D B P) (CA _C1 _A1 CG AG : ℝ) : Prop :=
  (ParA large₂ CA → OPO large₂ B → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : WeightFamilies.Wt D j), 8 * D.R.f * D.R.r + 4 ≤ w.n →
    Submodule.span B.KO ((X j h1 h2).shortTh w : Set (B.Cusp j w)) = ⊤ ∧
    ∃ S : Finset (B.Cusp j w),
      Submodule.span (𝓞 B.KO) (S : Set (B.Cusp j w)) = (X j h1 h2).shortTh w ∧
      ∀ g ∈ S, ∀ σ, Real.log (B.supN j w σ g) ≤
        WeightFamilies.PPv D large₂ CG AG * (1 + Real.log (absA w + w.n)) * (absA w + w.n)) ∧
  WeightFamilies.adm2 large₂ B CG AG

def adm3 (large₂ : SizeData₂ D) (X : Prov D B P) (CA Cf Af : ℝ) : Prop :=
  ParA large₂ CA → ∀ j (h1 : 1 ≤ j) (h2 : j < D.R.m), ∃ i : ℕ, 0 < i ∧
    ∃ et : B.Cusp j (wscalar D j (g0 D * i) (by unfold g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩)),
    et ≠ 0 ∧ (X j h1 h2.le).NonZeroComp _ et ∧
    (∀ la (y : (X j h1 h2.le).Pt la), ((2 * i * (X j h1 h2.le).phiC la y : ℝ) : EReal) ≤
      (X j h1 h2.le).vAt la y ((X j h1 h2.le).inc _ et)) ∧
    ∀ σ, Real.log (B.supN j _ σ et) / i ≤ WeightFamilies.PPv D large₂ Cf Af

def ArchimedeanSignatureMatching (large₂ : SizeData₂ D) (X : Prov D B P) (CA _C1 _A1 CW AW : ℝ) : Prop :=
  ParA large₂ CA → OPO large₂ B → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : WeightFamilies.Wt D j), 8 * D.R.f * D.R.r + 4 ≤ w.n →
    w.LastPos →
    (∃ S : Finset (B.Cusp j w),
      Submodule.span (𝓞 B.KO) (S : Set (B.Cusp j w)) = (X j h1 h2).thAll w ∧
      Real.log (S.card : ℝ) ≤ WeightFamilies.PPv D large₂ CW AW * w.n * (1 + Real.log (absA w + w.n)) ∧
      ∀ g ∈ S, ∀ σ, Real.log (B.supN j w σ g) ≤
        WeightFamilies.PPv D large₂ CW AW * (1 + Real.log (absA w + w.n)) * (absA w + w.n)) ∧
    Real.log ((X j h1 h2).rk w ((X j h1 h2).thAll w)) ≤
      WeightFamilies.PPv D large₂ CW AW * w.n * (1 + Real.log (absA w + w.n))

def adm5 (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (CL AL : ℝ) : Prop := WeightFamilies.Conclusion1 large₂ B CL AL

def adm6 (B : WeightFamilies.Prov D) (CRm : ℝ) : Prop := WeightFamilies.Conclusion2 B CRm

def adm7 (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (CRm Ck Ch Ah Cq Aq : ℝ) : Prop :=
  WeightFamilies.PointsLemma large₂ B CRm Ck Ch Ah Cq Aq

def admitted (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq : ℝ) : Prop :=
  adm1 B ∧ adm2 large₂ X H.CA H.C1 H.A1 K.CG K.AG ∧ adm3 large₂ X H.CA K.Cf K.Af ∧ ArchimedeanSignatureMatching large₂ X H.CA H.C1 H.A1 K.CW K.AW ∧
    adm5 large₂ B K.CL K.AL ∧ adm6 B K.CRm ∧ adm7 large₂ B K.CRm H.CK Ch Ah Cq Aq

def Stmt (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp)
    (Ch Ah Cq Aq C2 A2 CR Bx CT A : ℝ) : Prop :=
  admitted large₂ X K H Ch Ah Cq Aq → Conclusion1 large₂ X H C2 A2 CR CT ∧ Conclusion2 large₂ X H C2 A2 CR Bx CT A

abbrev ObjClass : Type 1 :=
  ∀ {D : D7} (_ : SizeData₂ D) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D), Prov D B P → Prop

structure Sel where
  Ch : KAdm → KHyp → ℝ
  Ah : DAdm → DHyp → ℝ
  C2 : KAdm → KHyp → ℝ → ℝ → ℝ
  A2 : DAdm → DHyp → ℝ → ℝ
  CR : DAdm → DHyp → ℝ → ℝ
  Bx : DAdm → DHyp → ℝ → ℝ

def UniformClosedFormStatement (𝒪 : ObjClass) : Prop :=
  ∃ s : Sel, ∀ (K : KAdm) (H : KHyp) (Cq Aq : ℝ), 2 ≤ K.CRm → ∀ CT eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ,
    ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (X : Prov D B P), 𝒪 large₂ B P X →
      large₂.sc.eps = eps → x0 ≤ large₂.sc.x → admitted large₂ X K H (s.Ch K H) (s.Ah K.deg H.deg) Cq Aq →
      Conclusion1 large₂ X H (s.C2 K H Cq Aq) (s.A2 K.deg H.deg Aq) (s.CR K.deg H.deg Aq) CT

def ClosedFormProjectorBound (𝒪 : ObjClass) : Prop :=
  ∀ A : ℝ, ∃ s : Sel, ∀ (K : KAdm) (H : KHyp) (Cq Aq : ℝ), 2 ≤ K.CRm → ∀ CT eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ,
    ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (X : Prov D B P), 𝒪 large₂ B P X →
      large₂.sc.eps = eps → x0 ≤ large₂.sc.x → admitted large₂ X K H (s.Ch K H) (s.Ah K.deg H.deg) Cq Aq →
      Conclusion2 large₂ X H (s.C2 K H Cq Aq) (s.A2 K.deg H.deg Aq) (s.CR K.deg H.deg Aq) (s.Bx K.deg H.deg Aq) CT A

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (BF : WeightFamilies.ProvF Fm)
  (PF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Prov (Fm.D x i) (BF x hx i) (PF x hx i))

def AdmF (K : KAdm) (H : KHyp) (Ch Ah Cq Aq : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, admitted (Fm.L x i) (XF x hx i) K H Ch Ah Cq Aq

def ConclusionF1 (H : KHyp) (C2 A2 CR : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Conclusion1 (Fm.L x i) (XF x hx i) H C2 A2 CR (Fm.Ct + 1)

def ConclusionF2 (H : KHyp) (C2 A2 CR Bx A : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Conclusion2 (Fm.L x i) (XF x hx i) H C2 A2 CR Bx (Fm.Ct + 1) A

end Family

def PeriodFamilyStatement (𝒪 : ObjClass) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR : ℝ) {eps : ℝ}
    (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) : Prop :=
  ∀ (BF : WeightFamilies.ProvF Fm) (PF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Prov (Fm.D x i) (BF x hx i) (PF x hx i)),
    (∀ x hx i, 𝒪 (Fm.L x i) (BF x hx i) (PF x hx i) (XF x hx i)) →
    AdmF Fm BF PF XF K H Ch Ah Cq Aq → ConclusionF1 Fm BF PF XF H C2 A2 CR

def DeterminantValueFamily (𝒪 : ObjClass) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR Bx A : ℝ) {eps : ℝ}
    (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) : Prop :=
  ∀ (BF : WeightFamilies.ProvF Fm) (PF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Prov (Fm.D x i) (BF x hx i) (PF x hx i)),
    (∀ x hx i, 𝒪 (Fm.L x i) (BF x hx i) (PF x hx i) (XF x hx i)) →
    AdmF Fm BF PF XF K H Ch Ah Cq Aq → ConclusionF2 Fm BF PF XF H C2 A2 CR Bx A

def ClosedSupNormFirstForm (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ s : Sel, Formalism.MainNotions.Closed 𝒞 (fun Fm CH => ∀ (K : KAdm) (H : KHyp) (Cq Aq : ℝ), 2 ≤ K.CRm →
    PeriodFamilyStatement 𝒪 K H (s.Ch K H) (s.Ah K.deg H.deg) Cq Aq (s.C2 K H Cq Aq) (s.A2 K.deg H.deg Aq) (s.CR K.deg H.deg Aq) Fm CH)

def ClosedFixedPowerForm (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ A : ℝ, ∃ s : Sel, Formalism.MainNotions.Closed 𝒞 (fun Fm CH => ∀ (K : KAdm) (H : KHyp) (Cq Aq : ℝ), 2 ≤ K.CRm →
    DeterminantValueFamily 𝒪 K H (s.Ch K H) (s.Ah K.deg H.deg) Cq Aq (s.C2 K H Cq Aq) (s.A2 K.deg H.deg Aq) (s.CR K.deg H.deg Aq)
      (s.Bx K.deg H.deg Aq) A Fm CH)

theorem ClosedSupNormFirstForm.fixed {𝒪 : ObjClass} {𝒞 : Formalism.MainNotions.FamClass} (h : ClosedSupNormFirstForm 𝒪 𝒞) (K : KAdm) (H : KHyp)
    (hK : 2 ≤ K.CRm) : ∃ Ch Ah : ℝ, ∀ Cq Aq : ℝ, ∃ C2 A2 CR : ℝ,
    Formalism.MainNotions.Closed 𝒞 (fun Fm CH => PeriodFamilyStatement 𝒪 K H Ch Ah Cq Aq C2 A2 CR Fm CH) := by
  obtain ⟨s, hs⟩ := h
  unfold Formalism.MainNotions.Closed at hs
  obtain ⟨ε1, hε1, hc⟩ := hs
  refine ⟨s.Ch K H, s.Ah K.deg H.deg, fun Cq Aq => ⟨s.C2 K H Cq Aq, s.A2 K.deg H.deg Aq, s.CR K.deg H.deg Aq, ?_⟩⟩
  unfold Formalism.MainNotions.Closed
  refine ⟨ε1, hε1, fun eps he1 he2 => ?_⟩
  obtain ⟨Kt, hKt⟩ := hc eps he1 he2
  exact ⟨Kt, fun Fm CH hC hL => hKt Fm CH hC hL K H Cq Aq hK⟩

theorem ClosedFixedPowerForm.fixed {𝒪 : ObjClass} {𝒞 : Formalism.MainNotions.FamClass} (h : ClosedFixedPowerForm 𝒪 𝒞) (K : KAdm) (H : KHyp) (A : ℝ)
    (hK : 2 ≤ K.CRm) : ∃ Ch Ah : ℝ, ∀ Cq Aq : ℝ, ∃ C2 A2 CR Bx : ℝ,
    Formalism.MainNotions.Closed 𝒞 (fun Fm CH => DeterminantValueFamily 𝒪 K H Ch Ah Cq Aq C2 A2 CR Bx A Fm CH) := by
  obtain ⟨s, hs⟩ := h A
  unfold Formalism.MainNotions.Closed at hs
  obtain ⟨ε1, hε1, hc⟩ := hs
  refine ⟨s.Ch K H, s.Ah K.deg H.deg, fun Cq Aq =>
    ⟨s.C2 K H Cq Aq, s.A2 K.deg H.deg Aq, s.CR K.deg H.deg Aq, s.Bx K.deg H.deg Aq, ?_⟩⟩
  unfold Formalism.MainNotions.Closed
  refine ⟨ε1, hε1, fun eps he1 he2 => ?_⟩
  obtain ⟨Kt, hKt⟩ := hc eps he1 he2
  exact ⟨Kt, fun Fm CH hC hL => hKt Fm CH hC hL K H Cq Aq hK⟩

theorem closed_first_form_of_uniform {𝒪 : ObjClass} (h : UniformClosedFormStatement 𝒪) (𝒞 : Formalism.MainNotions.FamClass) :
    ClosedSupNormFirstForm 𝒪 𝒞 := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, ?_⟩
  unfold Formalism.MainNotions.Closed
  refine ⟨1 / 53, by norm_num, fun eps he1 he2 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  intro K H Cq Aq hK BF PF XF hO hAd
  obtain ⟨x0, hx0⟩ := hs K H Cq Aq hK (Fm.Ct + 1) eps he1 (by linarith)
  obtain ⟨x0', hx0'⟩ := hAd
  refine ⟨max x0 x0', fun x hx hxx i => ?_⟩
  exact hx0 (Fm.D x i) (Fm.L x i) (BF x hx i) (PF x hx i) (XF x hx i) (hO x hx i) (Fm.L_eps x i)
    (by rw [Fm.L_x x i hx]; exact le_trans (le_max_left _ _) hxx)
    (hx0' x hx (le_trans (le_max_right _ _) hxx) i)

theorem closed_fixed_power_of_uniform {𝒪 : ObjClass} (h : ClosedFormProjectorBound 𝒪) (𝒞 : Formalism.MainNotions.FamClass) :
    ClosedFixedPowerForm 𝒪 𝒞 := by
  intro A
  obtain ⟨s, hs⟩ := h A
  refine ⟨s, ?_⟩
  unfold Formalism.MainNotions.Closed
  refine ⟨1 / 53, by norm_num, fun eps he1 he2 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  intro K H Cq Aq hK BF PF XF hO hAd
  obtain ⟨x0, hx0⟩ := hs K H Cq Aq hK (Fm.Ct + 1) eps he1 (by linarith)
  obtain ⟨x0', hx0'⟩ := hAd
  refine ⟨max x0 x0', fun x hx hxx i => ?_⟩
  exact hx0 (Fm.D x i) (Fm.L x i) (BF x hx i) (PF x hx i) (XF x hx i) (hO x hx i) (Fm.L_eps x i)
    (by rw [Fm.L_x x i hx]; exact le_trans (le_max_left _ _) hxx)
    (hx0' x hx (le_trans (le_max_right _ _) hxx) i)

def PageAt (large₂ : SizeData₂ D) (C2 A2 : ℝ) : Prop :=
  ∃ (Q : ParameterChoice' D large₂) (PT : ParamsT D large₂ Q), Formalism.MainNotions.SizesAt large₂ ∧ PT.CP = C2 ∧ PT.eP = A2

def TieC (K : KAdm) (H : KHyp) (Ch Ah _Cq Aq C2 A2 CR : ℝ) : Prop :=
  H.C1 = C2 ∧ H.A1 = A2 ∧ H.Cc = C2 ∧ H.Ac = A2 ∧ H.CRc = 7 ∧ CR = 7 ∧ K.CRm = 7 ∧ 12 ≤ A2 ∧
    K.AG ≤ 2 ∧ K.Af ≤ 2 ∧ K.AW ≤ 2 ∧ K.AL ≤ 4 ∧ 1 ≤ Ch ∧ 4 ≤ Ah ∧ Aq ≤ 11

theorem tieC_inhabited (CK CA CG Cf CW CL Cq C2 A2 : ℝ) (h : 12 ≤ A2) :
    TieC ⟨CG, 2, Cf, 2, CW, 2, CL, 4, 7⟩ ⟨CK, CA, C2, A2, C2, A2, 7⟩ 1 4 Cq 11 C2 A2 7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem cc_tie {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR : ℝ} (ht : TieC K H Ch Ah Cq Aq C2 A2 CR) (large₂ : SizeData₂ D) {j : ℕ}
    (wL : WeightFamilies.Wt D j) :
    cc D large₂ H.Cc H.Ac H.CRc wL = WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2 / (qq D : ℝ) := by
  obtain ⟨-, -, h1, h2, h3, h4, -⟩ := ht
  simp only [cc, h1, h2, h3, h4]

theorem pageAt_PP {large₂ : SizeData₂ D} {C2 A2 : ℝ} (h : PageAt large₂ C2 A2) :
    ∃ (Q : ParameterChoice' D large₂) (PT : ParamsT D large₂ Q), WeightFamilies.PPv D large₂ C2 A2 = PT.PP := by
  obtain ⟨Q, PT, -, hC, hA⟩ := h
  refine ⟨Q, PT, ?_⟩
  unfold WeightFamilies.PPv
  rw [PT.PP_eq, hC, hA]

theorem pageAt_fam {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {C2 A2 : ℝ} (hC : Fm.CP = C2) (hA : Fm.eP = A2) (x : ℝ) (hx : Fm.x1 < x)
    (i : Fm.Ix x) : PageAt (Fm.L x i) C2 A2 := by
  refine ⟨Fm.params x hx i, Fm.parT x hx i, Fm.sizes x hx i, ?_, ?_⟩
  · rw [← hC]
    unfold Formalism.MainNotions.FamP.CP
    rw [← Fm.parT_K x hx i]
    rfl
  · rw [← hA]
    unfold Formalism.MainNotions.FamP.eP
    rw [← Fm.parT_K x hx i]
    rfl

def RankScaledBoundOfParametersCondition (large₂ : SizeData₂ D) (X : Prov D B P) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    Hyp large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus → PageAt large₂ C2 A2 →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

theorem page_form_of_theorem_zero {large₂ : SizeData₂ D} {X : Prov D B P} {H : KHyp} {C2 A2 CR CT : ℝ}
    (h : Conclusion1 large₂ X H C2 A2 CR CT) : RankScaledBoundOfParametersCondition large₂ X H C2 A2 CR CT := by
  intro j h1 h2 S ka wL wF T nP nW h0 nus hH _
  exact h j h1 h2 S ka wL wF T nP nW h0 nus hH

theorem theorem_zero_of_page_form {large₂ : SizeData₂ D} {X : Prov D B P} {H : KHyp} {C2 A2 CR CT : ℝ} (hp : PageAt large₂ C2 A2)
    (h : RankScaledBoundOfParametersCondition large₂ X H C2 A2 CR CT) : Conclusion1 large₂ X H C2 A2 CR CT := by
  intro j h1 h2 S ka wL wF T nP nW h0 nus hH
  exact h j h1 h2 S ka wL wF T nP nW h0 nus hH hp

section FamilyT

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (BF : WeightFamilies.ProvF Fm)
  (PF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Prov (Fm.D x i) (BF x hx i) (PF x hx i))

def RankScaledBoundFamily (H : KHyp) (C2 A2 CR : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, RankScaledBoundOfParametersCondition (Fm.L x i) (XF x hx i) H C2 A2 CR (Fm.Ct + 1)

theorem page_form_family_of_theorem_zero (H : KHyp) (C2 A2 CR : ℝ) (h : ConclusionF1 Fm BF PF XF H C2 A2 CR) :
    RankScaledBoundFamily Fm BF PF XF H C2 A2 CR := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx hxx i => page_form_of_theorem_zero (hx0 x hx hxx i)⟩

theorem theorem_zero_family_of_page_form (H : KHyp) {C2 A2 : ℝ} (CR : ℝ) (hC : Fm.CP = C2) (hA : Fm.eP = A2)
    (h : RankScaledBoundFamily Fm BF PF XF H C2 A2 CR) : ConclusionF1 Fm BF PF XF H C2 A2 CR := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx hxx i => theorem_zero_of_page_form (pageAt_fam Fm hC hA x hx i) (hx0 x hx hxx i)⟩

end FamilyT

def RankScaledBoundConstrainedFamily (𝒪 : ObjClass) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR : ℝ) {eps : ℝ}
    (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) : Prop :=
  TieC K H Ch Ah Cq Aq C2 A2 CR →
  ∀ (BF : WeightFamilies.ProvF Fm) (PF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Prov (Fm.D x i) (BF x hx i) (PF x hx i)),
    (∀ x hx i, 𝒪 (Fm.L x i) (BF x hx i) (PF x hx i) (XF x hx i)) →
    AdmF Fm BF PF XF K H Ch Ah Cq Aq → RankScaledBoundFamily Fm BF PF XF H C2 A2 CR

theorem constrained_family_of_theorem_zero {𝒪 : ObjClass} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR : ℝ} {eps : ℝ}
    {Fm : Formalism.MainNotions.FamP eps} {CH : ℝ} (h : PeriodFamilyStatement 𝒪 K H Ch Ah Cq Aq C2 A2 CR Fm CH) :
    RankScaledBoundConstrainedFamily 𝒪 K H Ch Ah Cq Aq C2 A2 CR Fm CH := by
  intro _ BF PF XF hO hAd
  exact page_form_family_of_theorem_zero Fm BF PF XF H C2 A2 CR (h BF PF XF hO hAd)

theorem theorem_zero_family_of_constrained {𝒪 : ObjClass} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR : ℝ} {eps : ℝ}
    {Fm : Formalism.MainNotions.FamP eps} {CH : ℝ} (ht : TieC K H Ch Ah Cq Aq C2 A2 CR) (hC : Fm.CP = C2) (hA : Fm.eP = A2)
    (h : RankScaledBoundConstrainedFamily 𝒪 K H Ch Ah Cq Aq C2 A2 CR Fm CH) : PeriodFamilyStatement 𝒪 K H Ch Ah Cq Aq C2 A2 CR Fm CH := by
  intro BF PF XF hO hAd
  exact theorem_zero_family_of_page_form Fm BF PF XF H CR hC hA (h ht BF PF XF hO hAd)

def ClosedConstrainedRankScaledBound (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm CH => ∀ (K : KAdm) (H : KHyp) (Ch Ah Cq Aq : ℝ),
    RankScaledBoundConstrainedFamily 𝒪 K H Ch Ah Cq Aq Fm.CP Fm.eP 7 Fm CH)

theorem ClosedConstrainedRankScaledBound.closed_constrained_gives_family {𝒪 : ObjClass} {𝒞 : Formalism.MainNotions.FamClass} (h : ClosedConstrainedRankScaledBound 𝒪 𝒞) :
    Formalism.MainNotions.Closed 𝒞 (fun Fm CH => ∀ (K : KAdm) (H : KHyp) (Ch Ah Cq Aq : ℝ), TieC K H Ch Ah Cq Aq Fm.CP Fm.eP 7 →
      PeriodFamilyStatement 𝒪 K H Ch Ah Cq Aq Fm.CP Fm.eP 7 Fm CH) := by
  unfold ClosedConstrainedRankScaledBound at h
  unfold Formalism.MainNotions.Closed at h ⊢
  obtain ⟨ε1, hε1, hc⟩ := h
  refine ⟨ε1, hε1, fun eps he1 he2 => ?_⟩
  obtain ⟨Kt, hKt⟩ := hc eps he1 he2
  exact ⟨Kt, fun Fm CH hC hL K H Ch Ah Cq Aq ht =>
    theorem_zero_family_of_constrained ht rfl rfl (hKt Fm CH hC hL K H Ch Ah Cq Aq)⟩

end Formalism.MainNotions.WeightAlgebra

end
