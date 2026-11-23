import Mathlib
import Formalism.LocalToGlobal.Divisibility.RowLat
import Formalism.QuotientMetricDivisors.DivIntoDualShift
import Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundFull
import Formalism.ThetaSupremumBounds.DivIneqExplicit6
import Formalism.ThetaSupremumBounds.StatementCB

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
open Formalism.LatticeIndexTer (ph)

structure RecNums (J Pl : Type) [Fintype J] [Fintype Pl] [DecidableEq Pl] where

  TT : Finset Pl

  logT : ℝ

  aT : Pl → ℝ

  r : ℕ

  ν : J → Pl → Fin r → ℝ

  logH : J → Pl → ℝ

  x : ℝ

  eps : ℝ

  L : ℝ

  b : ℝ

  a : ℝ

  rd : ℝ

  La : ℝ

  B0 : ℝ

  Nc : ℝ

  m : ℝ

  f : ℝ

  k : ℝ

  Nn : ℝ

  S : ℝ

  tt : ℝ

  η : ℝ

  w'' : ℝ

  b' : ℝ

  lam0 : ℝ

  C0 : ℝ

  ce : ℝ

  Ch : ℝ

  nV : ℝ

  Lp : ℝ

  logOm : ℝ

  pq : J → ℝ

  w : J → Pl → ℝ

  eE : J → Pl → ℝ

  δ : J → Pl → ℝ

  weight_height_sum_le : ∀ j ρ, (∑ i, ph (ν j ρ i)) - logH j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ

  weight_sum_eq : ∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ

  p1 : 1 < x

  p2 : 0 < eps

  p3 : L = x ^ eps

  p4 : b = Real.exp L

  p5 : a = x * b

  p6 : 1 ≤ rd

  p7 : Real.log rd ≤ L

  p8 : Real.log x ≤ L

  p9 : La = Real.log (a * rd)

  p10 : B0 = f * m * b * x ^ eps

  p11 : 0 ≤ Nc

  p12 : (Fintype.card J : ℝ) = m

  p13 : (Fintype.card Pl : ℝ) ≤ f

  p14 : 1 ≤ m

  p15 : 1 ≤ f

  p16 : 1 ≤ k

  p17 : k + m ≤ Nn

  p18 : 0 ≤ S

  p19 : 0 ≤ tt

  p20 : 0 ≤ η

  p21 : ∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b

  p22 : ∀ j, |pq j - k| ≤ m

  p23 : |logOm| ≤ La

  p24 : m * lam0 ≤ b

  p25 : Nn ^ 2 ≤ b

  p26 : m ^ 3 * Nn ^ 2 * L ≤ b

  p27 : m * η * Nn * L ≤ b

  p28 : k * Nn ≤ b

  p29 : k * S ≤ w''

  p30 : m * (tt + 1) * η ≤ w''

  p31 : Nn * w'' ≤ b

  p32 : b' * Nn ≤ a

  p33 : m * k * b' ≤ a

  p34 : 0 ≤ b'

  p35 : 0 ≤ lam0

  p36 : 0 ≤ nV

  p37 : nV ≤ Nn

  p38 : 0 ≤ Lp

  c1 : 1 ≤ C0

  c2 : C0 ≤ ce

  c3 : 0 ≤ Ch

  c4 : Ch ≤ C0

  c5 : Ch * Lp ≤ C0 * La

  sE : ∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + Nn ^ 2 + m * (tt + 1) * η) * La

  sδ : ∀ j ρ, |δ j ρ| ≤ C0 * (w j ρ + k * (Nn + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))

namespace RecNums

variable {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl] (R : RecNums J Pl)

def hA : ℝ :=
  -(∑ t ∈ R.TT, R.aT t * R.logT) +
    R.Ch * ((R.TT.card : ℝ) * R.b' * R.Nn + R.f * (R.m * R.η + R.S) * R.Nn + R.f * R.Nn ^ 2) * R.La

def hB (j : J) : ℝ :=
  (∑ ρ, ((∑ i, ph (R.ν j ρ i)) - (∑ i, R.ν j ρ i) * R.logOm)) + R.Ch * R.f * R.Nn ^ 2 * (R.La + R.m ^ 3 * R.L)

def hX (j : J) : ℝ :=
  (∑ ρ, R.logH j ρ) - R.Ch * R.f * R.nV ^ 2 * R.Lp

def hu : ℝ := R.hA + ∑ j, (R.hB j - R.hX j)

def rhs : ℝ :=
  (∑ t ∈ R.TT, (R.m * (ph (R.aT t) - R.aT t * R.logOm) - R.aT t * R.logT)) +
    ((50 * R.C0 + 10) * ((R.TT.card : ℝ) * R.a * R.La) +
      60 * R.ce * (R.m * (R.x ^ R.eps * (R.B0 + R.Nc))))

def errB : ℝ :=
  R.ce * R.m * (R.x ^ R.eps * (R.B0 + R.Nc))

end RecNums

structure HtNums {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl] (R : RecNums J Pl) (Emb : Type) [Fintype Emb] where

  hPn : ℝ

  g0 : J → ℝ

  MainNotions : J → Emb → ℝ

  logOmτ : Pl → Emb → ℝ

  logth0 : Emb → ℝ

  logh : J → ℝ

  logh' : J → ℝ

  vv : ℝ

  logg : ℝ

  C2 : ℝ

  Cth : ℝ

  C4 : ℝ

  c5 : ℝ

  c6 : ℝ

  CT : ℝ

  C8 : ℝ

  Ce : ℝ

  ev : ℝ

  bT : Pl → ℝ

  nτ : Pl → ℝ

  lam1 : Pl → ℝ

  D0 : Pl → ℝ

  D1 : Pl → ℝ

  logc : Pl → ℝ

  logxi : Pl → ℝ

  Cev : ℝ

  i1 : ∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = R.logOm

  i2 : ∀ j s, MainNotions j s ≤ C2 * R.f * R.m ^ 2 * R.Nn ^ 2 * (logg + R.logT) + Ce * R.f * R.Nn ^ 2 * logg

  i3 : (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ Cth * R.L

  i4 : ∀ j, logh j ≤ C4 * R.f * R.Nn ^ 2 * (R.L + R.logT + logg)

  i5 : ∀ j, logh' j ≤ C4 * R.f * R.Nn ^ 2 * (R.L + R.logT + logg)

  i6 : ∀ j, 0 ≤ g0 j ∧ g0 j ≤ R.Nn ^ 2

  i7 : ∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * vv) ≤ c5 * R.La

  i8 : ∀ j τ, Real.log (2 * (∑ i, R.ν j τ i) + 2) ≤ c6 * R.La

  i9 : logg ≤ C8 * R.L

  i10 : 0 ≤ C2 ∧ 0 ≤ Cth ∧ 0 ≤ C4 ∧ 0 ≤ c5 ∧ 0 ≤ c6 ∧ 0 ≤ C8 ∧ 0 ≤ Ce

  t1 : hPn ≤ -(∑ τ, nτ τ * R.logT) + (∑ τ, (2 * logc τ + logxi τ)) + ev

  t2 : ∀ τ, logc τ ≤ (R.Nn - 1) * D1 τ * Real.log (2 * R.a)

  t3 : ∀ τ, logxi τ ≤ R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)

  t4 : ∀ τ, nτ τ = lam1 τ - D0 τ

  t5 : ∀ τ ∈ R.TT, lam1 τ = R.aT τ - (R.Nn - R.k) / 2

  t6 : ∀ τ, τ ∉ R.TT → R.S - (R.Nn - 1) / 2 ≤ lam1 τ

  t7 : ∀ τ, D0 τ ≤ R.S + R.m * R.η + (if τ ∈ R.TT then bT τ else 0)

  t8 : ∀ τ, D1 τ ≤ 3 * D0 τ + R.S + R.η

  t9 : ∀ τ ∈ R.TT, bT τ ≤ 2 * R.b'

  t10 : 0 ≤ R.logT ∧ R.logT ≤ CT * R.m * R.L ∧ 0 ≤ CT

  t11 : ev ≤ Cev * R.f * R.Nn ^ 2 * R.La ∧ 0 ≤ Cev

  k1 : 2 * (16 + CT + Cev) ≤ R.Ch

  k2 : Cth + c5 + 2 * c6 + 1 + 2 * C4 + 2 * Ce * C8 ≤ R.Ch

  k3 : 2 * (C2 + C4) * (CT + C8) ≤ R.Ch

def HtNums.sz {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl] {R : RecNums J Pl} {Emb : Type} [Fintype Emb]
    (H : HtNums R Emb) (j : J) (s : Emb) : ℝ :=
  Formalism.DimensionVariation.liftedMapLogSize R.ν H.g0 H.MainNotions H.logOmτ H.logth0 H.logh H.logh' H.vv j s

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}

structure ColChain {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem) where

  mm : ℕ

  lf : Bs.J → Fin mm

  c : Fin (mm + 1) → ℕ

  c0 : c 0 = Dc.a u

  X : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ

  X_unit : ∀ i v, IsUnit (X i v).det

  X_zero : ∀ v i j, X 0 v i j = Dc.Xc u v (Fin.cast c0 i) (Fin.cast c0 j)

  Kj : ∀ j : Fin mm, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K

  PtL : (Fin (c (Fin.last mm)) → K) →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)

  fact : ∀ (φ : Fin (Dc.a u) → K) (F : Fin (Df.nV Bs.μ0) → K),
    Dc.Pt u Bs.μ0 φ F = PtL ((chainMat Kj (Fin.last mm)).mulVec fun i => φ (Fin.cast c0 i)) F

structure CBData {m : ℕ} {c : Fin (m + 1) → ℕ} (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ)
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K) where

  AA : Fin (m + 1) → Type
  [fAA : ∀ i, Fintype (AA i)]

  Cl : ∀ i, AA i → Type
  [fCl : ∀ i a, Fintype (Cl i a)]

  W : Fin (m + 1) → InfinitePlace K → Type
  [nW : ∀ i v, NormedAddCommGroup (W i v)]
  [sW : ∀ i v, NormedSpace ℂ (W i v)]

  γ : ∀ i, (Σ a, Cl i a) → ℝ

  Φ : ∀ i v, (Fin (c i) → ℂ) → (Σ a, Cl i a) → W i v

  ε : ∀ (j : Fin m) (_ : InfinitePlace K), (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) → ℂ

  T : ∀ (j : Fin m) (v : InfinitePlace K), (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) → W j.castSucc v →L[ℂ] W j.succ v

  hcl : Fin (m + 1) → ℝ

  tmax : Fin m → InfinitePlace K → ℝ

  hyp : Formalism.DimensionVariation.CBHyp Xc Kj Cl W γ Φ ε T hcl tmax

attribute [instance] CBData.fAA CBData.fCl CBData.nW CBData.sW

def CBData.sq {m : ℕ} {c : Fin (m + 1) → ℕ} {Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ}
    {Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K} (D : CBData Xc Kj) (j : Fin m) (v : InfinitePlace K) : ℝ :=
  Formalism.DimensionVariation.cbSq (Fintype.card (D.AA j.castSucc)) (Fintype.card (D.AA j.succ)) (D.hcl j.castSucc) (D.hcl j.succ) (D.tmax j v)

def FoOf (P : IndefCore Df0 Df1 Dc Sp N) : ℝ :=
  ∑ j, ∑ y ∈ P.base.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)

def boundB (P : IndefCore Df0 Df1 Dc Sp N) (LG E3 : ℝ) (E2 : Bs.J → ℝ) : ℝ :=
  (∑ j, N.l3 j) + 2 * FoOf P + LG + (∑ j, (N.E1 j + E2 j)) + E3

def shiftZ (sg : HeightOneSpectrum (𝓞 K) → ℝ) : HeightOneSpectrum (𝓞 K) → ℤ := fun w => ⌊sg w⌋

def shiftLat {d : ℕ} (Nu : Submodule (𝓞 K) (Fin d → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ) :
    Submodule (𝓞 K) (Fin d → K) :=
  Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal (shiftZ sg) : Submodule (𝓞 K) K) Nu

structure DivInputs0 {Pl : Type} [Fintype Pl] [DecidableEq Pl] (P : IndefCore Df0 Df1 Dc Sp N) (R : RecNums Bs.J Pl)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ) where

  Nu_lat : Submodule.IsLattice K Nu

  sg_fin : (Function.support (shiftZ sg)).Finite

  Xc_unit : ∀ v, IsUnit (Dc.Xc u v).det

  a_pos : 0 < Dc.a u

  X0 : InfinitePlace K → Matrix (Fin (Df1.nV Bs.μ0)) (Fin (Df1.nV Bs.μ0)) ℂ

  base_matrix_det_unit : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df1.HV Bs.μ0).map v.embedding

  ch : ColChain Dc u

  hn : HtNums R (InfinitePlace K)

  nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
    (Pi.basisFun K (Fin (Df1.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn

  cb : CBData ch.X ch.Kj

  nKcb : ∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v

  eig6 : ∑ j, R.hX j ≤ ∑ j, N.l6 j

  eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df0.dQ t) → Fin (Df0.dQ t) → K

  heb : ∀ t w, IsLocBasis (Df0.abelian₂ t) w (eb t w)

  Sy : Finset (HeightOneSpectrum (𝓞 K))

  Sy_tw : P.base.Tw ⊆ Sy

  G0 : ∀ y, y ∉ Sy → vw y (Df0.Gm eb (P.base.μ y) y) = 0

  LG : ℝ

  E3 : ℝ

  E2 : Bs.J → ℝ

  gy : HeightOneSpectrum (𝓞 K) → ℝ

  ηy : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  bi : ∀ y ∈ Sy, (vw y (Df0.Gm eb (P.base.μ y) y) : ℝ) ≤ (P.base.D : ℝ) * gy y

  bLG : ∑ y ∈ Sy, lw y * gy y ≤ LG

  biv : ∀ y ∈ P.base.Tw, ∀ j, (jw (Df0.HT j (P.base.μ y)) y (Df0.Tl j (P.base.μ y)) : ℝ) ≤
    ((ramw y : ℝ) * N.J0 (P.base.μ y) y j) * (P.base.D : ℝ) + ηy y j

  borderedMinorImage : ∀ j, ∑ y ∈ P.base.Tw, lw y * ηy y j / (P.base.D : ℝ) ≤ E2 j

  twisted_third_sum_le : ∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3

  El3 : ℝ

  L3main : ∑ j, N.l3 j ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + El3

  errB : El3 + LG + (∑ j, (N.E1 j + E2 j)) + E3 ≤ R.errB

  Q : ℝ

  de0 : 0 ≤ N.de

  deQ : 3 * N.de * Q ≤ 1

  Q1 : 1 ≤ Q

  Qb : boundB P LG E3 E2 + N.hh + 28 * N.la ≤ Q

  la_le : N.la ≤ R.lam0

  constant_ge_twenty_eight : 28 ≤ R.C0

structure DivInputs {Pl : Type} [Fintype Pl] [DecidableEq Pl] (P : IndefCore Df0 Df1 Dc Sp N) (R : RecNums Bs.J Pl)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ) extends DivInputs0 P R u Nu sg where

  val2 : ∀ w, ∀ φ ∈ Nu, ∀ F ∈ Df1.Mt (P.cols.μ w),
    Dc.Pt u (P.cols.μ w) φ F = 0 ∨ sg w ≤ (vw w (Dc.Pt u (P.cols.μ w) φ F) : ℝ)

end Formalism.L2.DIV
