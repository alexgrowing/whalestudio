import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataKap
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace Formalism.MainNotions.placeRankTwoOne

open Formalism.BasicNotions NumberField IsDedekindDomain

def rdK (D : D7) : ℝ := Real.sqrt D.host.d

def pS (D : D7) (j : ℕ) : ℝ := (D.R.k : ℝ) + j - 1

def qS (D : D7) (j : ℕ) : ℝ := (D.R.m : ℝ) - j

def NN (D : D7) : ℝ := (D.R.N D.R.m : ℝ)

def wI (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ℤ := round (DV.wSz D j τ)

def normU (D : D7) (j : ℕ) (w : D.what₂.Tau → ℤ) : ℝ := ∑ τ, ∑ i, |(DV.kapW D j τ i : ℝ) - w τ|

def c1 (D : D7) (X : DivX D) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  -(∑ c, X.degHH j c τ) / (Fintype.card (X.Comp j) : ℝ)

def mainT (D : D7) (X : DivX D) (j : ℕ) (w : D.what₂.Tau → ℤ) : ℝ := ∑ τ, (w τ : ℝ) * c1 D X j τ

def logHk (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, Real.log (Real.Gamma (a i + n - i))) -
    ∑ i ∈ Finset.range n, ∑ l ∈ Finset.Ioo i n, Real.log (a i - a l + l - i)

def sumHk (D : D7) (j : ℕ) : ℝ :=
  ∑ τ, (logHk (D.R.sigW j).1 (DV.aPlus D j τ) +
    logHk (D.R.sigW j).2 (fun i => DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i)))

def TOL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  C * ((D.R.m : ℝ) * DV.wSz D j τ + D.R.k * large₂.Sc + D.R.k * large₂.etaSz +
    (D.R.m : ℝ) ^ 3 * (NN D + D.R.t) ^ 2 + D.R.m * D.R.t * large₂.etaSz) * large₂.sc.L *
    Real.log (Real.log large₂.sc.x)

def sumTOL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) (j : ℕ) : ℝ := ∑ τ, TOL D large₂ C j τ

def sumKer (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) : ℝ := ∑ τ, DV.kerPlace D large₂ u j τ

def sumKerAt (D : D7) (u : D.what₂.Word) (j : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  ∑ τ, ((∑ i ∈ Finset.range (D.R.N (j - 1)), phF (DV.nuRow D u j τ i)) -
    (∑ i ∈ Finset.range (D.R.N (j - 1)), DV.nuRow D u j τ i) * Real.log (D.gx.Om τ s))

def sumHook (D : D7) (j : ℕ) : ℝ := ∑ τ, ∑ i ∈ Finset.range (D.R.k - 1), phF (DV.aPlus D j τ i)

def hookR {N : ℕ} (nu : Fin N → ℝ) : ℝ :=
  (∏ i : Fin N, (((⌊nu i⌋.toNat + N - 1 - i : ℕ).factorial : ℕ) : ℝ)) /
    ∏ i : Fin N, ∏ l ∈ Finset.univ.filter (fun l => i < l),
      (((⌊nu i⌋ - ⌊nu l⌋ + (l : ℤ) - (i : ℤ) : ℤ)) : ℝ)

def sumLogHook (D : D7) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  ∑ τ, Real.log (hookR (fun a : Fin (D.R.N (j - 1)) => DV.nuRow D u j τ a))

def sumPhi (D : D7) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  ∑ τ, ∑ i ∈ Finset.range (D.R.N (j - 1)), phF (DV.nuRow D u j τ i)

def sumNuOm (D : D7) (u : D.what₂.Word) (j : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  ∑ τ, (∑ i ∈ Finset.range (D.R.N (j - 1)), DV.nuRow D u j τ i) * Real.log (D.gx.Om τ s)

def topMain (D : D7) (large₂ : SizeData₂ D) : ℝ :=
  ∑ t : D.host.TT, (phF (large₂.aT t) - (large₂.aT t : ℝ) * large₂.logOm)

def degLine (D : D7) (r : (D.what₂.LL →+* ℂ) → ℝ) (ρ : D.what₂.places.Pl → ℝ) : ℝ :=
  (∑ᶠ w, ρ w * lw D.what₂.LL (D.plEq w)) - (∑ σ, Real.log (r σ)) / (Module.finrank ℚ D.what₂.LL : ℝ)

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

def idOf (D : D7) (τ : D.what₂.Tau)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.what₂.LL) D.what₂.LL :=
  Submodule.span (𝓞 D.what₂.LL) ((embTau D τ) '' {x | x ∈ I})

def ddEK (D : D7) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

def idMul {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (I : Submodule (𝓞 K) K) (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  Submodule.span (𝓞 K) {y | ∃ a ∈ I, ∃ z ∈ M, y = a • z}

open Classical in

def detW (D : D7) (τ : D.what₂.Tau) : D.what₂.Tau → Fin D.R.r → ℤ :=
  fun τ' _ => if τ' = τ then -1 else 0

def IsNV {D : D7} (X : DivX D) (j : ℕ) (c : X.Comp j) (τ : D.what₂.Tau)
    (s : X.geo.Fn (X.Yv j c)) : Prop :=
  s ≠ 0 ∧ s ∈ X.geo.H0 (X.Yv j c) (X.Lw j c (detW D τ)) ∧
    s⁻¹ ∈ X.geo.H0 (X.Yv j c) (-(X.Lw j c (detW D τ)))

structure Loc (D : D7) (X : DivX D) where

  lieCK : HLat D.what₂.LL
  lieCK_good : lieCK.Good
  lieCK_rank : lieCK.rank = 1

  ell : D.what₂.Tau → HLat D.what₂.LL
  ell_good : ∀ τ, (ell τ).Good
  ell_rank : ∀ τ, (ell τ).rank = 1

  ellIso : ∀ τ, lieCK.V ≃ₗ[D.what₂.LL] (ell τ).V
  ellIso_lat : ∀ τ, (ell τ).L = (idMul (idOf D τ (D.host.AA0 * ddEK D)) lieCK.L).map
      ((ellIso τ).toLinearMap.restrictScalars (𝓞 D.what₂.LL))
  ellIso_norm : ∀ τ v (z : lieCK.V),
    Formalism.HermitianLatticesTheory.normAt (ell τ).b (ell τ).X v (ellIso τ z) = Formalism.HermitianLatticesTheory.normAt lieCK.b lieCK.X v z

  ell_Om : ∀ τ, D.gx.logOmMean τ = (ell τ).mu

  eH : ∀ τ, Submodule (𝓞 D.what₂.LL) (ell τ).V

  eH_eq : ∀ τ, eH τ = (idMul (idOf D τ D.host.AA0) lieCK.L).map
      ((ellIso τ).toLinearMap.restrictScalars (𝓞 D.what₂.LL))

  Comp_ne : ∀ j, 1 ≤ j → j ≤ D.R.m → Nonempty (X.Comp j)

  PtF : ∀ j, X.Comp j → D.what₂.places.Pl → Type
  PtF_ne : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c w, Nonempty (PtF j c w)
  pts_ne : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c σ, Nonempty (X.geo.pts (X.Yv j c) σ)

  vHT : ∀ j c, D.what₂.Tau → ∀ w, PtF j c w → ℚ

  vSub : ∀ j c, D.what₂.Tau → ∀ w, PtF j c w → ℚ

  vLie : ∀ j c, D.what₂.Tau → ∀ w, PtF j c w → ℚ

  metH : ∀ j c τ σ, X.geo.Met (X.Yv j c) σ (X.Lw j c (detW D τ))

  vF : ∀ j c, D.what₂.Tau → ∀ w, X.geo.Fn (X.Yv j c) → PtF j c w → ℝ

  vF_smul : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c τ w (a : D.what₂.LL) (f : X.geo.Fn (X.Yv j c)) y, a ≠ 0 → IsNV X j c τ f →
    vF j c τ w (a • f) y = (vAdd (D.plEq w) a : ℝ) + vF j c τ w f y

  degHH_def : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c τ (s : X.geo.Fn (X.Yv j c)), IsNV X j c τ s →
    ∀ (r : (D.what₂.LL →+* ℂ) → ℝ) (ρ : D.what₂.places.Pl → ℝ), (∀ σ, 0 < r σ) →
      (∀ σ y, X.geo.pn (X.Yv j c) σ _ (metH j c τ σ) (X.geo.cx (X.Yv j c) σ s) y = r σ ^ 2) →
      (∀ w y, vF j c τ w s y = ρ w) → (Function.support ρ).Finite →
      X.degHH j c τ = degLine D r ρ

  thSup : ∀ u i, (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → ℝ

variable (D : D7) (large₂ : SizeData₂ D) (X : DivX D) (Lc : Loc D X)

def HHPsi {D : D7} {X : DivX D} (Lc : Loc D X) (τ : D.what₂.Tau) :
    Submodule (𝓞 D.what₂.LL) (Lc.ell τ).V :=
  idMul (idOf D τ (ddEK D)) (Lc.eH τ)

def dFl (j : ℕ) : ℝ :=
  (pS D j - qS D j) / 2 * large₂.logOm + qS D j * (2 * Real.log (rdK D) - Real.log D.host.rdE)

def LL0 : ℝ :=
  Real.log (large₂.sc.b * D.host.rdE) * Real.log (Real.log large₂.sc.x) + |large₂.logDerivativeAtOne| + Real.log large₂.sc.x

def dimY : ℕ := D.R.f * (D.R.r.choose 2)

def PP (CP AP : ℝ) : ℝ :=
  CP * ((D.R.f : ℝ) * (D.R.r : ℝ) * large₂.sc.L) ^ AP

theorem PP_eq_par {D : D7} {large₂ : SizeData₂ D} {P : ParameterChoice' D large₂} (T : ParamsT D large₂ P) : PP D large₂ T.CP T.eP = T.PP := by
  rw [T.PP_eq]
  rfl

def TT (CP AP : ℝ) : ℝ := (⌈PP D large₂ CP AP ^ 2 * (dimY D : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ)

theorem TT_nonneg (CP AP : ℝ) : 0 ≤ TT D large₂ CP AP := by
  unfold TT
  positivity

theorem TT_le_nat (CP AP : ℝ) (n : ℕ)
    (h : PP D large₂ CP AP ^ 2 * (dimY D : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) ≤ (n : ℝ)) : TT D large₂ CP AP ≤ (n : ℝ) := by
  unfold TT
  exact_mod_cast Nat.ceil_le.mpr h

def Gc (CP AP : ℝ) : ℝ :=
  (TT D large₂ CP AP + dimY D + 2) * (TT D large₂ CP AP + dimY D + 2 + 2 * (D.R.r : ℝ))

def SizeSettingLemmaThree (Cn CP AP Cq : ℝ) (j : ℕ) (w : D.what₂.Tau → ℤ) : Prop :=
  1 ≤ j ∧ j ≤ D.R.m ∧
  (∀ τ (i : Fin D.R.r), i.val < D.R.k - 1 →
    -(Cn * ((D.R.r : ℝ) + D.R.t)) ≤ (DV.kapW D j τ i : ℝ) - w τ ∧
      (DV.kapW D j τ i : ℝ) - w τ ≤ large₂.Sc + Cn * ((D.R.r : ℝ) + D.R.t)) ∧
  (∀ τ (i : Fin D.R.r), D.R.k - 1 ≤ i.val →
    |(DV.kapW D j τ i : ℝ)| ≤ large₂.etaSz + large₂.Sc + Cn * ((D.R.r : ℝ) + D.R.t)) ∧
  (∀ τ (i l : Fin D.R.r), i.val < (D.R.sigW j).1 → (D.R.sigW j).1 ≤ l.val →
    (DV.kapW D j τ l : ℝ) < DV.kapW D j τ i) ∧
  (∀ τ, large₂.sc.w'' D.R.n ≤ (w τ : ℝ) ∧ (w τ : ℝ) ≤ 2 * large₂.sc.b) ∧
  PP D large₂ CP AP * (large₂.Sc + large₂.etaSz) ≤ large₂.sc.w'' D.R.n ∧
  (∀ τ (i i' : Fin D.R.r), i'.val = i.val + 1 → i'.val ≠ (D.R.sigW j).1 →
    Gc D large₂ CP AP ≤ (DV.kapW D j τ i : ℝ) - DV.kapW D j τ i') ∧
  (∀ τ (i i' : Fin D.R.r), D.R.k - 1 ≤ i.val → D.R.k - 1 ≤ i'.val → i ≠ i' →
    (i.val < (D.R.sigW j).1 ↔ i'.val < (D.R.sigW j).1) →
    LevelStarExponents.h0 large₂ - 1 ≤ |(DV.kapW D j τ i : ℝ) - DV.kapW D j τ i'|) ∧
  (∀ τ (i l : Fin D.R.r), i.val < (D.R.sigW j).1 → (D.R.sigW j).1 ≤ l.val →
    LevelStarExponents.h0 large₂ ≤ (DV.kapW D j τ i : ℝ) - DV.kapW D j τ l) ∧
  4 * TT D large₂ CP AP ^ 2 ≤ LevelStarExponents.h0 large₂ ∧
  PP D large₂ CP AP * TT D large₂ CP AP * (D.R.r : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * dimY D ≤ LevelStarExponents.h0 large₂ ∧
  PP D large₂ CP AP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (dimY D : ℝ) ^ 3 ≤ large₂.sc.b ∧
  PP D large₂ CP AP * TT D large₂ CP AP * (dimY D : ℝ) ^ 2 * Real.log large₂.sc.b ≤ large₂.sc.b ∧
  PP D large₂ CP AP * Real.sqrt large₂.sc.b ≤ large₂.sc.b ∧
  |large₂.logDerivativeAtOne| ≤ large₂.sc.x ^ large₂.sc.eps ∧
  large₂.sc.x ^ Cq < (D.host.q : ℝ) ∧ large₂.sc.x ^ Cq < (D.host.d : ℝ) ∧
  Real.log D.host.q ≤ large₂.sc.x ^ (large₂.sc.eps / 4) ∧ Real.log D.host.d ≤ large₂.sc.x ^ (large₂.sc.eps / 4) ∧
  (∀ i, D.host.g i % LevelStarExponents.condE D = 1 ∧ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧
    Real.log (D.host.g i) ≤ Cn * large₂.sc.L) ∧
  10 ^ 3 ≤ CP ∧ CP ^ 20 ≤ zBase large₂ ∧ 12 ≤ AP ∧
  (∃ (P : ParameterChoice' D large₂) (T : ParamsT D large₂ P), Formalism.MainNotions.SizesAt large₂ ∧ PP D large₂ CP AP ≤ T.PP ∧ TT D large₂ CP AP ≤ (T.TO : ℝ))

def opSq (u : D.what₂.Word) (i : ℕ) (h : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ) : ℝ :=
  Formalism.HN.opNormAt ((D.fm u).lat i).b ((D.fm u).lat i).X ((D.fm u).lat (i + 1)).b
    ((D.fm u).lat (i + 1)).X (InfinitePlace.mk s) ((D.fm u).KL i h) ^ 2

def kLe (u : D.what₂.Word) (i : ℕ) (h : (D.fm u).KRat i) (B : ℝ) : Prop :=
  ∏ s : D.what₂.LL →+* ℂ, opSq D u i h s ≤ Real.exp ((Module.finrank ℚ D.what₂.LL : ℝ) * B)

def thMean : ℝ := DV.meanE D (fun s => Real.log (D.gx.thOne s ^ 2))

def errK (C : ℝ) (u : D.what₂.Word) : ℝ :=
  C * D.R.f * (D.R.m : ℝ) ^ 2 * NN D ^ 2 *
    (large₂.sc.L + Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * (D.mem u).A.T))

def Sizes (Cs : ℝ) : Prop :=
  0 ≤ Real.log D.host.v ∧ Real.log D.host.rdE ≤ large₂.sc.L ∧ |large₂.logDerivativeAtOne| ≤ large₂.sc.L ∧
  Real.log (4 * large₂.sc.x) ≤ large₂.sc.L ∧ 1 ≤ Real.log (Real.log large₂.sc.x) ∧
  (∀ i, Real.log (D.host.g i : ℝ) ≤ Cs * large₂.sc.L) ∧
  (∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ Cs * D.R.m * large₂.sc.L) ∧
  large₂.Cc ≤ Cs ∧
  (∀ τ (hk : 2 ≤ D.R.k), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
    (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = (D.hc τ).v ⟨D.R.k - 2, by omega⟩ - 1 / 2) ∧
  4 * NN D ^ 3 ≤ large₂.etaSz ∧ (D.R.t : ℝ) ≤ large₂.etaSz ∧
  (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * large₂.etaSz ≤ large₂.sc.w'' D.R.n ∧
  (D.R.k : ℝ) * large₂.Sc ≤ large₂.sc.w'' D.R.n ∧
  (∀ t, (large₂.bT t : ℝ) ≤ 2 * large₂.sc.b')

def GapsA : Prop :=
  2 * NN D ^ 3 + (D.R.t : ℝ) < LevelStarExponents.h0 large₂ ∧
  ∀ τ (i : ℕ) (h : i + 1 < D.R.m),
    LevelStarExponents.h0 large₂ ≤ (((D.hc τ).b ⟨i + 1, h⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ)

theorem distCentre (D : D7) (τ : D.what₂.Tau) (j : Fin D.R.m) :
    ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).e j - (D.hc τ).b j ∧
      ∀ h : j.1 + 1 < D.R.m, ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨j.1 + 1, h⟩ - (D.hc τ).e j :=
  ⟨(D.hc τ).gap_be j, fun h => (D.hc τ).gap_eb j h⟩

theorem GapsA_of {D : D7} {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) : GapsA D large₂ := by
  cases P
  rename_i z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45
  unfold GapsA NN
  refine ⟨?_, fun τ i h => (z19 τ i h).1⟩
  have h3 : (0:ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  have ht : (0:ℝ) ≤ (D.R.t : ℝ) := by positivity
  linarith [z15.2.2.2.2.1]

def adm1 : Prop := Lc.lieCK.mu = dlogL D 0 + Real.log (D.host.d : ℝ) / 2

def HodgeTateDeterminant : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ w, ∃ c0 : ℚ, ∀ c y, Lc.vSub j c τ w y - Lc.vHT j c τ w y = c0

def DeRhamFreeness : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ w, ∃ c0 : ℚ, ∀ c y, Lc.vSub j c τ w y = c0

def RamifiedDeterminantBound : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ w c y,
    |(Lc.vLie j c τ w y : ℝ)| ≤ 2 * qS D j * X.vdd (D.what₂.places.resChar w) τ

def ThetaSupBound (C : ℝ) : Prop :=
  ∀ u i L L', i + 1 ≤ D.R.m → Lc.thSup u i L L' ≤ C * D.R.f * NN D ^ 2 * large₂.sc.L

def adm3 (C : ℝ) : Prop :=
  ThetaSupBound D large₂ X Lc C ∧
  (∀ u i, i ≤ D.R.m →
    (Fintype.card ((D.mem u).C.cls i) : ℝ) ≤ Real.exp (C * D.R.f * NN D ^ 2 *
      (large₂.sc.L + Real.log ((D.mem u).A.T : ℝ) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)))) ∧
  (∀ u i c, i ≤ D.R.m →
    (Nat.card ((D.mem u).C.stab i c) : ℝ) ≤ Real.exp (C * D.R.f * NN D ^ 2 * large₂.sc.L))

def LiftSizeWithHook (C : ℝ) : Prop :=
  ∀ u i (h : (D.fm u).KRat i), i + 1 ≤ D.R.m → ∀ s,
    opSq D u i h s ≤ Real.exp (sumLogHook D u (i + 1) - sumNuOm D u (i + 1) s +
      (D.R.f : ℝ) * D.R.N i * D.R.N (i + 1) * Real.log (D.gx.thOne s ^ 2) + errK D large₂ C u)

def HookStirlingBound (C : ℝ) : Prop :=
  ∀ u i, i + 1 ≤ D.R.m → sumLogHook D u (i + 1) ≤ sumPhi D u (i + 1) + errK D large₂ C u

def LiftSizeAtEmbedding (C : ℝ) : Prop :=
  ∀ u i (h : (D.fm u).KRat i), i + 1 ≤ D.R.m → ∀ s,
    opSq D u i h s ≤ Real.exp (sumKerAt D u (i + 1) s +
      (D.R.f : ℝ) * D.R.N i * D.R.N (i + 1) * Real.log (D.gx.thOne s ^ 2) + errK D large₂ C u)

theorem lift_size_of_hook_and_stirling {D : D7} {large₂ : SizeData₂ D} {C C' : ℝ} (h : LiftSizeWithHook D large₂ C) (h2 : HookStirlingBound D large₂ C') :
    LiftSizeAtEmbedding D large₂ (C + C') := by
  intro u i hK hi s
  refine (h u i hK hi s).trans (Real.exp_le_exp.mpr ?_)
  have h3 := h2 u i hi
  have e1 : sumKerAt D u (i + 1) s = sumPhi D u (i + 1) - sumNuOm D u (i + 1) s := by
    unfold sumKerAt sumPhi sumNuOm
    rw [← Finset.sum_sub_distrib]
  have e2 : errK D large₂ (C + C') u = errK D large₂ C u + errK D large₂ C' u := by
    unfold errK
    ring
  rw [e1, e2]
  linarith

def GenusOneThetaNorm (C : ℝ) : Prop := thMean D ≤ C * large₂.sc.L

def adm5 (C : ℝ) : Prop :=
  Rows.LamPDef D.what₂ → GapsA D large₂ → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ →
    0 < D.what₂.lamP D.what₂.mu0 j σ ∧
    ∀ s, |X.logLam j σ s - sumHk D j| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 *
      Real.log (large₂.sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

def adm6 (Cn CP AP Cq C : ℝ) : Prop :=
  ∀ j (w : D.what₂.Tau → ℤ), SizeSettingLemmaThree D large₂ Cn CP AP Cq j w → 0 < (X.MjH j).rank →
    mainT D X j w - C * LL0 D large₂ * normU D j w - large₂.sc.b ≤ -(X.MjH j).lcv / 2 / ((X.MjH j).rank : ℝ)

def iwahoriAdmissibleSet (Cn CP AP Cq : ℝ) : Prop :=
  DV.KapDef D → ∀ j, 1 ≤ j → j ≤ D.R.m → SizeSettingLemmaThree D large₂ Cn CP AP Cq j (wI D j)

def RankEqualsDimension : Prop := DV.MjRank D X

def Conclusion1 : Prop := D.gx.OmValue D.host.v large₂.logDerivativeAtOne

def Conclusion2 (C : ℝ) : Prop :=
  (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ w, ∃ c0 : ℚ, ∀ c y, Lc.vHT j c τ w y = c0) ∧
  (∀ τ, HHPsi Lc τ = (Lc.ell τ).L) ∧
  (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ w c y,
    |(Lc.vLie j c τ w y : ℝ)| ≤ C * qS D j * X.vdd (D.what₂.places.resChar w) τ)

def PointsLemma : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (c : X.Comp j) τ,
    (∃ s : X.geo.Fn (X.Yv j c), IsNV X j c τ s ∧
      ∃ (r : (D.what₂.LL →+* ℂ) → ℝ) (ρ : D.what₂.places.Pl → ℝ),
        (∀ σ, 0 < r σ) ∧
        (∀ σ y, X.geo.pn (X.Yv j c) σ _ (Lc.metH j c τ σ) (X.geo.cx (X.Yv j c) σ s) y = r σ ^ 2) ∧
        (∀ w y, Lc.vF j c τ w s y = ρ w) ∧ (Function.support ρ).Finite ∧
        degLine D r ρ = dFl D large₂ j) ∧
    X.degHH j c τ = dFl D large₂ j

def FrobeniusOrbitPlaceCount : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (c : X.Comp j) τ, X.degHH j c τ = dFl D large₂ j

theorem degree_value_of_determinant {D : D7} {large₂ : SizeData₂ D} {X : DivX D} {Lc : Loc D X} (h : PointsLemma D large₂ X Lc) : FrobeniusOrbitPlaceCount D large₂ X := by
  intro j hj hj' c τ
  exact (h j hj hj' c τ).2

def Conclusion4 (C : ℝ) : Prop :=
  ∀ u i (h : (D.fm u).KRat i), i + 1 ≤ D.R.m →
    kLe D u i h (sumKer D large₂ u (i + 1) +
      (D.R.f : ℝ) * D.R.N i * D.R.N (i + 1) * thMean D + errK D large₂ C u)

def Conclusion5 (Cs C : ℝ) : Prop :=
  Rows.LamPDef D.what₂ → GapsA D large₂ → Sizes D large₂ Cs → ∀ j, 1 ≤ j → j ≤ D.R.m →
    ∀ σ : (D.what₂.LL →+* ℂ) → _, (∀ s, D.what₂.isot j (σ s) ≠ ⊥) →
      (∀ s, 0 < D.what₂.lamP D.what₂.mu0 j (σ s)) ∧
      |DV.meanE D (fun s => X.logLam j (σ s) s) - sumHook D j| ≤
        C * D.R.f * ((NN D + D.R.t) ^ 2 + large₂.Sc + D.R.m * large₂.etaSz) * large₂.sc.L

def Conclusion6 (Cs C : ℝ) : Prop :=
  Rows.LamPDef D.what₂ → DV.KapDef D → GapsA D large₂ → Sizes D large₂ Cs → 0 < D.what₂.D0 →
    ∀ u i (h : (D.fm u).KRat i), i + 1 ≤ D.R.m →
      ∀ σ : (D.what₂.LL →+* ℂ) → _, (∀ s, D.what₂.isot (i + 1) (σ s) ≠ ⊥) →
        kLe D u i h (DV.meanE D (fun s => X.logLam (i + 1) (σ s) s) -
          (X.MjH (i + 1)).lcv / (D.what₂.D0 : ℝ) +
          topMain D large₂ + sumTOL D large₂ C (i + 1) + 2 * large₂.sc.b)

def IntegralityFromMetric : Prop := adm1 D X Lc → Conclusion1 D large₂
def HodgeTateFromSandwich (C2 : ℝ) : Prop := HodgeTateDeterminant D X Lc ∧ DeRhamFreeness D X Lc ∧ RamifiedDeterminantBound D X Lc → Conclusion2 D X Lc C2

def TowerRallisLemma : Prop := Conclusion1 D large₂ → Conclusion2 D X Lc 2 → PointsLemma D large₂ X Lc
def ThetaChernBoundOfLastLine (C3 CZ CH C4 : ℝ) : Prop :=
  adm3 D large₂ X Lc C3 ∧ LiftSizeWithHook D large₂ CZ ∧ HookStirlingBound D large₂ CH → Conclusion1 D large₂ → Conclusion4 D large₂ C4
def GGFromIrreducibility (CA Cs C5 : ℝ) : Prop := adm5 D large₂ X CA → Conclusion5 D large₂ X Cs C5

def CompNe : Prop := ∀ j, 1 ≤ j → j ≤ D.R.m → Nonempty (X.Comp j)

def ShareFromInputs (Cn CP AP Cq C6 CT C4 Cs C5 C : ℝ) : Prop :=
  CompNe D X → iwahoriAdmissibleSet D large₂ Cn CP AP Cq ∧ adm6 D large₂ X Cn CP AP Cq C6 ∧ RankEqualsDimension D X ∧ GenusOneThetaNorm D large₂ CT →
    FrobeniusOrbitPlaceCount D large₂ X → Conclusion4 D large₂ C4 → Conclusion5 D large₂ X Cs C5 → Conclusion6 D large₂ X Cs C

abbrev LocF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i)

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : LocF Fm)

def admF1 : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), adm1 (Fm.D x i) (Fm.X x i) (XF x hx i)
def DeterminantFamily : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), HodgeTateDeterminant (Fm.D x i) (Fm.X x i) (XF x hx i)
def DeRhamFreenessFamily : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), DeRhamFreeness (Fm.D x i) (Fm.X x i) (XF x hx i)
def RamifiedFamily : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), RamifiedDeterminantBound (Fm.D x i) (Fm.X x i) (XF x hx i)
def admF3 : Prop :=
  ∃ C x0, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i, adm3 (Fm.D x i) (Fm.L x i) (Fm.X x i) (XF x hx i) C
def HookSizeFamily : Prop := ∃ C x0, ∀ x, x0 ≤ x → ∀ i, LiftSizeWithHook (Fm.D x i) (Fm.L x i) C
def StirlingHookFamilySomeConstant : Prop := ∃ C x0, ∀ x, x0 ≤ x → ∀ i, HookStirlingBound (Fm.D x i) (Fm.L x i) C
def LiftSizeFamily : Prop := ∃ C x0, ∀ x, x0 ≤ x → ∀ i, LiftSizeAtEmbedding (Fm.D x i) (Fm.L x i) C
def ThetaNormFamily : Prop := ∃ C x0, ∀ x, x0 ≤ x → ∀ i, GenusOneThetaNorm (Fm.D x i) (Fm.L x i) C
def admF5 : Prop := ∃ C x0, ∀ x, x0 ≤ x → ∀ i, adm5 (Fm.D x i) (Fm.L x i) (Fm.X x i) C

def admF6 (Cn CP AP Cq : ℝ) : Prop :=
  ∃ C x0, ∀ x, x0 ≤ x → ∀ i, adm6 (Fm.D x i) (Fm.L x i) (Fm.X x i) Cn CP AP Cq C

def SlopeSettingFamily (Cn CP AP Cq : ℝ) : Prop :=
  ∃ x0, ∀ x, x0 ≤ x → ∀ i, iwahoriAdmissibleSet (Fm.D x i) (Fm.L x i) Cn CP AP Cq
def CompNeF : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, CompNe (Fm.D x i) (Fm.X x i)

def RankFamilyEventually : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, RankEqualsDimension (Fm.D x i) (Fm.X x i)

def ConclusionF1 : Prop := ∀ x, Fm.x1 < x → ∀ i, Conclusion1 (Fm.D x i) (Fm.L x i)

def ConclusionF2 (C : ℝ) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion2 (Fm.D x i) (Fm.X x i) (XF x hx i) C
def ConclusionF3 : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PointsLemma (Fm.D x i) (Fm.L x i) (Fm.X x i) (XF x hx i)
def DegreeValueFamily : Prop := ∀ x, Fm.x1 < x → ∀ i, FrobeniusOrbitPlaceCount (Fm.D x i) (Fm.L x i) (Fm.X x i)
def FamilyEstimateFour : Prop := ∃ C x0, ∀ x, x0 ≤ x → ∀ i, Conclusion4 (Fm.D x i) (Fm.L x i) C

def ConclusionF5 : Prop := ∀ Cs, ∃ C x0, ∀ x, x0 ≤ x → ∀ i, Conclusion5 (Fm.D x i) (Fm.L x i) (Fm.X x i) Cs C
def ConclusionF6 : Prop := ∀ Cs, ∃ C x0, ∀ x, x0 ≤ x → ∀ i, Conclusion6 (Fm.D x i) (Fm.L x i) (Fm.X x i) Cs C

def PeriodFamilyStatement : Prop := admF1 Fm XF → ConclusionF1 Fm
def DeterminantValueFamily : Prop := DeterminantFamily Fm XF ∧ DeRhamFreenessFamily Fm XF ∧ RamifiedFamily Fm XF → ConclusionF2 Fm XF 2
def FlatLineDegreeFamilyStatement : Prop := ConclusionF1 Fm → ConclusionF2 Fm XF 2 → ConclusionF3 Fm XF
def LiftNormFamilyStatement : Prop := admF3 Fm XF ∧ HookSizeFamily Fm ∧ StirlingHookFamilySomeConstant Fm → ConclusionF1 Fm → FamilyEstimateFour Fm
def DegreeBoundFamilyStatement : Prop := admF5 Fm → ConclusionF5 Fm
def SlopeBoundFamilyStatement (Cn CP AP Cq : ℝ) : Prop :=
  CompNeF Fm → SlopeSettingFamily Fm Cn CP AP Cq ∧ admF6 Fm Cn CP AP Cq ∧ RankFamilyEventually Fm ∧ ThetaNormFamily Fm →
    DegreeValueFamily Fm → FamilyEstimateFour Fm → ConclusionF5 Fm → ConclusionF6 Fm

def LiftNormFamilyWithConstant (C : ℝ) : Prop :=
  ∃ x0, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i, adm3 (Fm.D x i) (Fm.L x i) (Fm.X x i) (XF x hx i) C
def HookSizeFamilyWithConstant (C : ℝ) : Prop := ∃ x0, ∀ x, x0 ≤ x → ∀ i, LiftSizeWithHook (Fm.D x i) (Fm.L x i) C
def StirlingHookFamily (C : ℝ) : Prop := ∃ x0, ∀ x, x0 ≤ x → ∀ i, HookStirlingBound (Fm.D x i) (Fm.L x i) C
def ThetaNormFamilyWithConstant (C : ℝ) : Prop := ∃ x0, ∀ x, x0 ≤ x → ∀ i, GenusOneThetaNorm (Fm.D x i) (Fm.L x i) C
def DegreeBoundFamilyWithConstant (C : ℝ) : Prop := ∃ x0, ∀ x, x0 ≤ x → ∀ i, adm5 (Fm.D x i) (Fm.L x i) (Fm.X x i) C
def SlopeSettingFamilyWithConstants (Cn CP AP Cq C : ℝ) : Prop :=
  ∃ x0, ∀ x, x0 ≤ x → ∀ i, adm6 (Fm.D x i) (Fm.L x i) (Fm.X x i) Cn CP AP Cq C
def HeckeSizeFamilyWithConstant (C : ℝ) : Prop := ∃ x0, ∀ x, x0 ≤ x → ∀ i, Conclusion4 (Fm.D x i) (Fm.L x i) C
def KernelSizeFamilyWithConstant (Cs C : ℝ) : Prop := ∃ x0, ∀ x, x0 ≤ x → ∀ i, Conclusion5 (Fm.D x i) (Fm.L x i) (Fm.X x i) Cs C
def SlopeFamilyWithConstants (Cs C : ℝ) : Prop := ∃ x0, ∀ x, x0 ≤ x → ∀ i, Conclusion6 (Fm.D x i) (Fm.L x i) (Fm.X x i) Cs C

def HeckeSizeStatementWithConstants (C3 CZ CH C4 : ℝ) : Prop :=
  LiftNormFamilyWithConstant Fm XF C3 ∧ HookSizeFamilyWithConstant Fm CZ ∧ StirlingHookFamily Fm CH → ConclusionF1 Fm → HeckeSizeFamilyWithConstant Fm C4
def DegreeBoundFamilyConstants (CA Cs C5 : ℝ) : Prop := DegreeBoundFamilyWithConstant Fm CA → KernelSizeFamilyWithConstant Fm Cs C5
def SlopeFamilyStatement (Cn CP AP Cq C6 CT C4 Cs C5 C : ℝ) : Prop :=
  CompNeF Fm → SlopeSettingFamily Fm Cn CP AP Cq ∧ SlopeSettingFamilyWithConstants Fm Cn CP AP Cq C6 ∧ RankFamilyEventually Fm ∧ ThetaNormFamilyWithConstant Fm CT →
    DegreeValueFamily Fm → HeckeSizeFamilyWithConstant Fm C4 → KernelSizeFamilyWithConstant Fm Cs C5 → SlopeFamilyWithConstants Fm Cs C

end Fam

abbrev LocClass : Type 1 :=
  ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps), LocF Fm → Prop

def ClosedPeriodValue (𝒞 : Formalism.MainNotions.FamClass) (𝒴 : LocClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ XF : LocF Fm, 𝒴 Fm XF → PeriodFamilyStatement Fm XF)

def ClosedDeterminantValue (𝒞 : Formalism.MainNotions.FamClass) (𝒴 : LocClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ XF : LocF Fm, 𝒴 Fm XF → DeterminantValueFamily Fm XF)

def ClosedLiftNorm (𝒞 : Formalism.MainNotions.FamClass) (𝒴 : LocClass) : Prop :=
  ∃ Cf : ℝ → ℝ → ℝ → ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ =>
    ∀ XF : LocF Fm, 𝒴 Fm XF →
      ∀ C3 CZ CH : ℝ, HeckeSizeStatementWithConstants Fm XF C3 CZ CH (Cf C3 CZ CH))

def ClosedProportionality (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ Cf : ℝ → ℝ → ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ CA Cs : ℝ, DegreeBoundFamilyConstants Fm CA Cs (Cf CA Cs))

def ClosedSlopeBound (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ Cf : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ =>
    ∀ Cq C6 CT C4 Cs C5 : ℝ,
      SlopeFamilyStatement Fm (Fm.CYL + 1) Fm.CP Fm.eP Cq C6 CT C4 Cs C5 (Cf C6 CT C4 Cs C5))

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) (𝒴 : LocClass) : Prop :=
  ∀ Cq : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ =>
    (∀ XF : LocF Fm, 𝒴 Fm XF →
      PeriodFamilyStatement Fm XF ∧ DeterminantValueFamily Fm XF ∧ LiftNormFamilyStatement Fm XF) ∧
      DegreeBoundFamilyStatement Fm ∧ SlopeBoundFamilyStatement Fm (Fm.CYL + 1) Fm.CP Fm.eP Cq)

def ClosedFlatLineDegree (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ConclusionF1 Fm → DegreeValueFamily Fm)

end Formalism.MainNotions.placeRankTwoOne

end
