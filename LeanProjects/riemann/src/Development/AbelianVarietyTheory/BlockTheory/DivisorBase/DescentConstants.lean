import Mathlib
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Foundations.TableDegreeElevenProduct

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

open Formalism.BasicNotions Formalism.MainNotions Finset

def cOne : ℝ := 8

def cThree : ℝ := 94

def cSix : ℝ := 32

def ceilEight (n : ℕ) : ℕ := 8 * ((n + 7) / 8)

theorem ceilEight_spec (n : ℕ) : 8 ∣ ceilEight n ∧ n ≤ ceilEight n ∧ ∀ a, 8 ∣ a → n ≤ a → ceilEight n ≤ a := by
  unfold ceilEight
  refine ⟨⟨_, rfl⟩, by omega, fun a ha h => by omega⟩

section Numbers

variable (D : D7) (L : SizeData₂ D)

def lrd : ℝ := Real.log D.host.rdE

def pp (j : ℕ) : ℕ := (D.R.sigW j).1

def qq (j : ℕ) : ℕ := (D.R.sigW j).2

def dY : ℝ := (placeRankTwoOne.dimY D : ℝ)

def dX (j : ℕ) : ℕ := D.R.f * pp D j * qq D j

def cTw (j : ℕ) : ℕ := ceilEight (max (D.R.r + (dX D j + 1).choose 2 + 2) (8 * D.R.f * D.R.r + 4))

def nCol (j : ℕ) : ℕ :=
  ceilEight (max (D.R.f * (pp D j * (pp D j + 1) + qq D j * (qq D j + 1))) (8 * D.R.f * D.R.r + 4))

def eZero (j : ℕ) : ℝ := (D.R.f : ℝ) * D.R.r * ((cTw D j : ℝ) + 4 * D.R.r)

def cFlat (j : ℕ) : ℝ := |placeRankTwoOne.dFl D L j|

def bigR : ℝ := D.host.rdE ^ 7

def degStar : ℝ := 7 * (D.R.f : ℝ) * D.R.k * L.sc.b

def expQ : ℕ := sInf {c : ℕ | bigR D ^ 7 * degStar D L ^ 2 ≤ (3 : ℝ) ^ (2 * c)}

def levQ : ℕ := 3 ^ (2 * expQ D L)

def radOne : ℝ := bigR D * degStar D L

def expC : ℕ := sInf {c : ℕ | bigR D ^ 8 * degStar D L ^ 2 ≤ (3 : ℝ) ^ c ∧ max 4 (2 * expQ D L) ≤ c}

def levDeep : ℕ := D.host.g 0 * D.host.g 1 * (3 ^ expC D L * 5 ^ expC D L)

theorem expQ_spec : bigR D ^ 7 * degStar D L ^ 2 ≤ (3 : ℝ) ^ (2 * expQ D L) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (bigR D ^ 7 * degStar D L ^ 2) (by norm_num : (1 : ℝ) < 3)
  have : n ∈ {c : ℕ | bigR D ^ 7 * degStar D L ^ 2 ≤ (3 : ℝ) ^ (2 * c)} :=
    hn.le.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  exact Nat.sInf_mem ⟨n, this⟩

theorem expC_spec : bigR D ^ 8 * degStar D L ^ 2 ≤ (3 : ℝ) ^ expC D L ∧ max 4 (2 * expQ D L) ≤ expC D L := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (bigR D ^ 8 * degStar D L ^ 2) (by norm_num : (1 : ℝ) < 3)
  have : n + max 4 (2 * expQ D L) ∈
      {c : ℕ | bigR D ^ 8 * degStar D L ^ 2 ≤ (3 : ℝ) ^ c ∧ max 4 (2 * expQ D L) ≤ c} :=
    ⟨hn.le.trans (pow_le_pow_right₀ (by norm_num) (by omega)), by omega⟩
  exact Nat.sInf_mem ⟨_, this⟩

def shareW (g : ℕ) : ℝ :=
  3 * (D.R.f : ℝ) / g + 23 * D.R.f * Real.log g * (g : ℝ) ^ (-(1 : ℝ) / 2) +
    2 * D.R.f * D.R.m * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log D.R.r) / ((g : ℝ) - 1)) +
    (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log D.R.r))

def del : ℝ := shareW D (D.host.g 0) + shareW D (D.host.g 1)

def kap (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := if h : i < D.R.r then DV.kapW D j τ ⟨i, h⟩ else 0

def wAn (j : ℕ) (τ : D.what₂.Tau) : ℤ := kap D j τ (D.R.k - 2)

def uAn (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := kap D j τ i - wAn D j τ

def nrm (v : ℕ → ℤ) : ℝ := ∑ i ∈ range D.R.r, |(v i : ℝ)|

def nKap (j : ℕ) : ℝ := ∑ τ, nrm D (kap D j τ)

def nU (j : ℕ) : ℝ := ∑ τ, nrm D (uAn D j τ)

def sumW (j : ℕ) : ℝ := ∑ τ, (wAn D j τ : ℝ)

def deW (j i : ℕ) : ℤ := if i < pp D j then 0 else -1

def canW (j i : ℕ) : ℤ :=
  if i < pp D j then (qq D j : ℤ) - pp D j + 1 + 2 * i else -(pp D j : ℤ) - qq D j + 1 + 2 * ((i : ℤ) - pp D j)

def aW (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uAn D j τ i - (cTw D j : ℤ) * deW D j i - canW D j i

def degW (v : D.what₂.Tau → ℕ → ℤ) : ℝ :=
  ∏ τ, ∏ l ∈ range D.R.r, ∏ i ∈ range l, ((v τ i : ℝ) - v τ l)

def shift : ℝ := (D.R.nV : ℝ) / 2 * D.R.f * D.R.r * (Real.log (2 * Real.pi) / 2 + lrd D)

def nOne (j : ℕ) : ℝ := (D.R.f : ℝ) * D.R.nV * (cFlat D L j + 3 * D.R.m * lrd D)

theorem nU_eq (j : ℕ) : nU D j = placeRankTwoOne.normU D j (wAn D j) := by
  unfold nU placeRankTwoOne.normU nrm
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [uAn, kap, i.2]

theorem uAn_anchor (j : ℕ) (τ : D.what₂.Tau) : uAn D j τ (D.R.k - 2) = 0 := sub_self _

end Numbers

section Run

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

def ppTsq : ℝ :=
  max (1.2e9 * (D.R.r : ℝ) ^ 2)
    (max (448 * cOne * Q.PP * D.R.f * D.R.m) (32 * cThree * cSix * Q.PP * D.R.f * D.R.m))

def tN : ℕ := ⌈ppTsq Q * dY D ^ 2 * D.R.k / D.R.m⌉₊

def tR : ℝ := (tN Q : ℝ)

def gapMin : ℝ := (tR Q + dY D + 2) * (tR Q + dY D + 2 + 2 * D.R.r)

def gapOne (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ :=
  (aW D j τ i - aW D j τ (i + 1)) / ((tN Q + placeRankTwoOne.dimY D + 1 : ℕ) : ℤ)

def uOne (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ :=
  (∑ l ∈ Ico i (D.R.k - 2), gapOne Q j τ l) - ∑ l ∈ Ico (D.R.k - 2) i, gapOne Q j τ l

def uPr (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uOne Q j τ i - 3 * (D.R.r : ℤ) * deW D j i

def rhoB (j : ℕ) : ℝ := 1 - degW D (uPr Q j) / degW D (uOne Q j)

def zed (j : ℕ) : ℝ := 7 * (dY D ^ 2 / tR Q + dY D * rhoB Q j)

def epsR (j : ℕ) : ℝ := 7 * dY D ^ 2 / tR Q + 3 / 2 * dY D * rhoB Q j

def xZero (j : ℕ) : ℝ := dY D * (2 * dY D + 5 + rhoB Q j * tR Q) / ((1 - rhoB Q j) * (tR Q - dY D))

theorem uOne_anchor (j : ℕ) (τ : D.what₂.Tau) : uOne Q j τ (D.R.k - 2) = 0 := by simp [uOne]

def numBase (j : ℕ) : OT.Num where
  D := placeRankTwoOne.dimY D
  DX := dX D j
  f := D.R.f
  r := D.R.r
  m := D.R.m
  L := L.sc.L
  j := qq D j
  nW := Q.nWn
  Np := nCol D j
  lrd := lrd D
  LL := |L.logDerivativeAtOne|
  lM := Real.log (levDeep D L)
  lg := Real.log ((D.host.g 0 : ℝ) * D.host.g 1)
  lg1 := max (Real.log (D.host.g 0)) (Real.log (D.host.g 1))
  lp := max (Real.log D.host.pde) (Real.log D.host.pde')
  ld := Real.log D.host.d
  l4 := Real.log (max (4 * (D.R.n : ℝ) ^ 2) ((D.host.QS : ℝ) ^ 2 / 4) * D.host.q * D.host.d)
  l2q := Real.log ((D.host.QS : ℝ) * D.host.q * D.host.d)
  lx := Real.log L.sc.x
  llx := Real.log (Real.log L.sc.x)
  n := D.R.nV
  w := L.sc.b ^ 2
  a := nKap D j - (D.R.f : ℝ) * D.R.r * D.R.nV / 2
  ka := nKap D j
  u1 := ∑ τ, nrm D (uOne Q j τ)
  DF := degStar D L
  DFs := degStar D L
  RTc := bigR D * tR Q * (bigR D * Q.PP * degStar D L ^ 2 / levQ D L)
  lh := 0
  lNc := 0
  lpi := 0
  lmu := 0
  lmu1 := 0
  V := 0
  hb := 0
  logGenusConstant := 0
  dS := 0
  rS := 0
  dP := 0
  rP := 0
  lNA := 0
  Om := 0
  nu := 0
  lc := 0
  leE := 0
  ln0 := 0
  c1 := 0
  sc1 := 0
  G1 := 0
  CL := 0
  lR := 0
  rho := 0
  dp := 0
  gC := 0

def numAt (j : ℕ) : OT.Num := (numBase Q j).hat

def Reading (j : ℕ) (N : OT.Num) : Prop := N.admitted ∧ N.hat = numAt Q j

theorem numAt_hat (j : ℕ) : (numAt Q j).hat = numAt Q j := rfl

def ppE (D : D7) (N : OT.Num) : ℝ := N.PPp + 1 + lrd D

structure LogSizeBounds (j : ℕ) : Prop where
  lev : Real.log (levQ D L) ≤ 30 * L.sc.L ∧ Real.log (radOne D L) ≤ 30 * L.sc.L ∧
    Real.log ((3 : ℝ) ^ expC D L) ≤ 30 * L.sc.L ∧ Real.log (levDeep D L) ≤ 30 * L.sc.L
  T_le : tN Q ≤ Q.TO
  T_kap : 5 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * tR Q ^ 2 ≤ nKap D j
  pair_matrix_transpose : Q.PP ^ 3 * tR Q ^ 2 ≤ L.sc.b
  host : |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps ∧ lrd D + |L.logDerivativeAtOne| ≤ 2 * L.sc.L ∧
    ∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1 ∧ ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ D.host.g i
  w_win : ∀ τ, wj D j τ ≤ wAn D j τ ∧ (wAn D j τ : ℝ) ≤ wj D j τ + L.Sc + (D.R.r : ℝ) / 2 ∧
    L.sc.w'' D.R.n ≤ wAn D j τ ∧ (wAn D j τ : ℝ) ≤ 2 * L.sc.b
  shape : ∀ τ i, i < D.R.r →
    (i < D.R.k - 1 → 0 ≤ uAn D j τ i ∧ (uAn D j τ i : ℝ) ≤ L.Sc) ∧
    (D.R.k - 1 ≤ i → |(kap D j τ i : ℝ)| ≤ L.etaSz + (D.R.r : ℝ) / 2)
  u_size : ∀ τ,
    (D.R.m : ℝ) * (wAn D j τ - L.etaSz - (D.R.r : ℝ) / 2 - 1) ≤ nrm D (uAn D j τ) ∧
    nrm D (uAn D j τ) ≤ ((D.R.k : ℝ) - 1) * (L.Sc + D.R.r + D.R.t + 1) +
      D.R.m * (wAn D j τ + L.etaSz + (D.R.r : ℝ) / 2 + 1) ∧
    ((D.R.k : ℝ) - 1) * (L.Sc + D.R.r + D.R.t + 1) + D.R.m * (wAn D j τ + L.etaSz + (D.R.r : ℝ) / 2 + 1) ≤
      2 * (D.R.m * wAn D j τ + D.R.k * L.Sc + D.R.k * L.etaSz)
  kap_size : ∀ τ, nrm D (kap D j τ) ≤
    ((D.R.k : ℝ) - 1) * (wAn D j τ + L.Sc + D.R.r + D.R.t + 1) + D.R.m * (L.etaSz + (D.R.r : ℝ) / 2)
  kap_u : nKap D j ≤ 2 * (D.R.k : ℝ) / D.R.m * nU D j ∧ nKap D j ≤ 4 * (D.R.k : ℝ) / D.R.m * nU D j
  gap_compact : ∀ τ i, i + 1 < D.R.r → i + 1 ≠ pp D j → gapMin Q ≤ ((kap D j τ i - kap D j τ (i + 1) : ℤ) : ℝ)
  gap_node : ∀ τ i, D.R.k - 1 ≤ i → i + 1 < D.R.r → i + 1 ≠ pp D j →
    LevelStarExponents.h0 L - 1 ≤ ((kap D j τ i - kap D j τ (i + 1) : ℤ) : ℝ)
  gap_bar : j < D.R.m → ∀ τ,
    ((kap D j τ (pp D j - 1) - kap D j τ (pp D j) : ℤ) : ℝ) = LevelStarExponents.h0 L + D.R.r - 1
  u_le : nU D j ≤ cOne * D.R.f * D.R.m * L.sc.b
  kap_le : nKap D j ≤ cSix * D.R.f * D.R.k * L.sc.b
  u_ge : ∀ τ, (D.R.m : ℝ) * wAn D j τ / 2 ≤ nrm D (uAn D j τ)
  D_ge : 2 ≤ dY D
  T_20 : 20 * dY D ≤ tR Q
  height_ge_four_sq : 4 * tR Q ^ 2 ≤ LevelStarExponents.h0 L

structure ConstLines (j : ℕ) (N : OT.Num) : Prop where
  ties : Q.PP = Q.CP * zBase L ^ 12 ∧ Q.Dp = placeRankTwoOne.dimY D ∧ N.Z = zBase L ∧ N.LL0 = placeRankTwoOne.LL0 D L
  const_bound_le_six_sq : placeRankTwoOne.LL0 D L ≤ 6 * L.sc.L ^ 2
  cFlat_le : cFlat D L j ≤ 8.5 * D.R.r * L.sc.L
  cTw_le : (cTw D j : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4
  nCol_le : nCol D j ≤ 16 * D.R.f * D.R.r ^ 2 + 8
  D_le : dY D ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2
  T_rows : 2 * (D.R.r : ℝ) + dY D ≤ tR Q ∧ 3 * dY D + 5 ≤ tR Q ∧ 6 * dY D + 10 ≤ tR Q ∧ dY D ^ 2 ≤ tR Q ∧
    Real.log (tR Q) ≤ L.sc.L ∧ tR Q ≤ L.sc.b ∧ 1.2e9 * D.R.r * dY D ^ 2 ≤ tR Q
  ppT_le : ppTsq Q ≤ Q.PP ^ 2
  sign : 0 ≤ N.o ∧ 0 ≤ N.PPp ∧ 0 ≤ N.PPpp ∧ 0 ≤ N.CL ∧ 0 ≤ lrd D
  ppE_le : ppE D N ≤ Q.PP
  eight : 8 * N.PPp ≤ Q.PP
  ppp_le : N.PPpp ≤ Q.PP
  ppp_ge : 32 * N.PPp ≤ N.PPpp
  o_le : N.o ≤ N.PPpp
  ph_le : N.PPh ≤ N.PPpp
  cle : N.CL * placeRankTwoOne.LL0 D L * eZero D j ≤ N.PPp / 10

structure RunLines (j : ℕ) (N : OT.Num) : Prop where
  h_one : 4 * dY D + 4 ≤ tR Q
  h_two : 4 * ((cTw D j : ℝ) + 2 * D.R.r + tR Q + dY D + 1) ≤ LevelStarExponents.h0 L ∧ 24 * (D.R.r : ℝ) * tR Q ≤ LevelStarExponents.h0 L
  h_three : ∀ τ, 4 * ((L.etaSz + L.Sc + D.R.r) + L.Sc + cTw D j + 2 * D.R.r) + 20 * D.R.r * tR Q ≤ wAn D j τ
  h_five : ∀ τ i, i < D.R.r → |(uAn D j τ i : ℝ)| + cTw D j + 4 * D.R.r ≤ 2 * L.sc.b
  log_bound_le_sqrt : tR Q * dY D ^ 2 * Real.log L.sc.b ≤ Real.sqrt L.sc.b
  TPP : tR Q * Q.PP ≤ Real.sqrt L.sc.b
  height : (∀ τ i, i < D.R.r → |(uPr Q j τ i : ℝ)| / (LevelStarExponents.h0 L / (4 * tR Q)) ≤ 8 * L.sc.b / LevelStarExponents.h0 L) ∧
    Real.log (4 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (1 + 8 * L.sc.b / LevelStarExponents.h0 L)) ≤ 2 * L.sc.L + 4
  height_ge_run_term : 768 * cThree * cSix * tR Q * D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * dY D * N.PPp ≤ LevelStarExponents.h0 L
  height_ge_epsilon_term : 2304 * cOne * tR Q * D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * dY D * ppE D N ≤ LevelStarExponents.h0 L
  w_run : 384 * cThree * cSix * D.R.r * (D.R.f : ℝ) ^ 2 * D.R.m * (D.R.k : ℝ) ^ 2 * dY D * tR Q * N.PPp ≤
    L.sc.w'' D.R.n
  w_eps : 1152 * cOne * D.R.r * (D.R.f : ℝ) ^ 2 * D.R.m * (D.R.k : ℝ) ^ 2 * dY D * tR Q * ppE D N ≤
    L.sc.w'' D.R.n
  b_ge : Q.CbN * D.R.r * D.R.m * D.R.k * Q.PP ^ 2 * dY D ^ 3 ≤ L.sc.b
  primes : 6 * (D.R.k : ℝ) / D.R.m ≤ D.host.q / Real.log D.host.q ∧
    6 * (D.R.k : ℝ) / D.R.m ≤ D.host.d / Real.log D.host.d
  deg_pos : 0 < degW D (uOne Q j) ∧ 0 < degW D (uPr Q j)
  rho_mem : 0 ≤ rhoB Q j ∧ rhoB Q j ≤ 6 * (D.R.r : ℝ) * D.R.f *
    ((D.R.m : ℝ) ^ 2 * (2 * tR Q) / LevelStarExponents.h0 L + D.R.m * D.R.k * tR Q / L.sc.w'' D.R.n)
  rho_small : dY D * rhoB Q j ≤ 1 / (64 * cThree * cSix) ∧ rhoB Q j ≤ 1 / (10 * dY D) ∧
    dY D ^ 2 / tR Q ≤ 1 / 1.2e9 ∧ zed Q j ≤ 1 / 2
  n_two : cThree * N.PPp * nKap D j * dY D ^ 2 / tR Q ≤ L.sc.b / 32
  n_three : cThree * N.PPp * nKap D j * (dY D * rhoB Q j) ≤ L.sc.b / 32
  n_four : tR Q * N.PPpp ≤ L.sc.b / 32
  n_five : N.CL * placeRankTwoOne.LL0 D L * eZero D j ≤ L.sc.b / 32

structure DescentLines (j : ℕ) (N : OT.Num) : Prop where
  proviso : xZero Q j ≤ 1 / 10 ∧ rhoB Q j ≤ 1 / 4
  eps_b : epsR Q j * ppE D N * nKap D j ≤ L.sc.b / 8
  CL_le : 35 * L.sc.L ≤ nKap D j
  PP_le : Q.PP ≤ L.sc.b / 8 ∧ Q.PP ≤ Real.sqrt L.sc.b
  eps_small : dY D ^ 2 / tR Q ≤ 1 / 28 ∧ dY D * rhoB Q j ≤ 1 / 28 ∧ 0 ≤ epsR Q j ∧ epsR Q j ≤ 1 / 4 + 3 / 56
  del_mem : 0 ≤ del D ∧ del D ≤ Real.exp (-L.sc.x ^ (L.sc.ez / 7)) ∧ del D ≤ 1 / 12
  flat : (qq D j : ℝ) * sumW D j ≤ 2 * nU D j ∧ lrd D ≤ placeRankTwoOne.LL0 D L ∧ L.sc.L ≤ placeRankTwoOne.LL0 D L ∧ 1 ≤ nU D j
  cols : (D.R.f : ℝ) * D.R.r * D.R.nV ≤ 2 * nKap D j ∧ 100 * zBase L * D.R.nV ≤ L.sc.b
  shift_le : shift D ≤ 2 * zBase L * D.R.nV ∧ shift D ≤ (1 + lrd D) * nKap D j
  del_fk : 3072 * N.PPp * D.R.f * D.R.k * del D ≤ 1
  del_b : 12 * del D * N.PPp * nKap D j ≤ L.sc.b / 8
  o_del : N.o + 12 * del D * N.PPp * nKap D j ≤ L.sc.b / 4
  nOne_le : nOne D L j ≤ 14.5 * zBase L * D.R.nV
  rest : 14.5 * zBase L * D.R.nV + (2 * zBase L * D.R.nV + 35 * L.sc.L) + 122 * zBase L ^ 2 ≤ L.sc.b / 4

def ParamLines (j : ℕ) (N : OT.Num) : Prop :=
  LogSizeBounds Q j ∧ ConstLines Q j N ∧ RunLines Q j N ∧ DescentLines Q j N

def DelStrong (D : D7) (L : SizeData₂ D) (j : ℕ) (N : OT.Num) : Prop :=
  24 * del D * ppE D N * nKap D j ≤ L.sc.b / 8

theorem strong_arith {δ e A PP K fk b : ℝ} (hδ : 0 ≤ δ) (hδe : δ ≤ e) (hA : 0 ≤ A) (h16 : 16 * A ≤ PP)
    (hK : K ≤ 32 * fk * b) (hfk : 0 ≤ fk) (hb : 0 ≤ b) (h : 385 * PP * fk * e ≤ 1) :
    24 * δ * A * K ≤ b / 8 := by
  have h1 : 24 * δ * A * K ≤ 24 * δ * A * (32 * fk * b) := mul_le_mul_of_nonneg_left hK (by positivity)
  have h2 : δ * (16 * A) * fk ≤ e * PP * fk :=
    mul_le_mul_of_nonneg_right (mul_le_mul hδe h16 (by positivity) (hδ.trans hδe)) hfk
  have h3 : δ * A * fk ≤ 1 / 6144 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h3 hb]

structure Choice (j : ℕ) : Prop where
  kap_def : DV.KapDef D
  sizes : SizesAt L
  e_eq : Q.eP = 12
  one_le_CP : 1000 ≤ Q.CP
  Z_ge : (10 ^ 10 * Q.CP) ^ 20 ≤ zBase L
  x_ge : 2 * L.sc.x ^ (L.sc.ez / 7) ≤ L.sc.x ^ (L.sc.ez / 6) ∧
    2 * (L.Ct + 4) * Real.log L.sc.x + 6 ≤ L.sc.x ^ (L.sc.ez / 6)
  ranks : (D.R.m : ℝ) ≤ Real.sqrt L.sc.x ∧ L.sc.x ^ (2 + 8 * L.sc.eps) / 2 ≤ D.R.n ∧
    (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) ∧ (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (9 / 2 + 10 * L.sc.eps)
  logd : L.sc.x ^ (L.sc.ez / 5) * (Real.log L.sc.x / L.sc.J) ^ 2 / 2 < Real.log D.host.d
  thin : L.sc.b ^ (4 / 5 : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n ∧ L.sc.b ^ (4 / 5 : ℝ) * L.Sc ≤ L.sc.w'' D.R.n
  w_up : ∀ τ, wj D j τ + L.Sc + D.R.r ≤ 2 * L.sc.b
  w_low : ∀ τ, L.sc.w'' D.R.n ≤ wj D j τ
  thick : ∃ τ, L.sc.b ≤ wj D j τ
  u_max : ∀ τ i, i < D.R.r → |(uAn D j τ i : ℝ)| + cTw D j + 4 * D.R.r ≤ 2 * L.sc.b
  logg : ∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1
  rd : lrd D + |L.logDerivativeAtOne| ≤ 2 * L.sc.L
  cols : 10 ^ 4 * zBase L * D.R.nV ≤ L.sc.b
  lev : Real.log (levQ D L) ≤ 3 * L.sc.L ∧ Real.log (radOne D L) ≤ 2 * L.sc.L ∧
    Real.log ((3 : ℝ) ^ expC D L) ≤ 3 * L.sc.L ∧ Real.log ((15 : ℝ) ^ expC D L) ≤ 7.4 * L.sc.L
  cloud : ∀ τ (i : ℕ) (h : i + 1 < D.R.k - 1),
    (D.hc τ).v ⟨i, by omega⟩ - (D.hc τ).v ⟨i + 1, h⟩ = 4 * (D.s.Del : ℚ)
  nodes : ∀ τ (i : ℕ) (h : i + 1 < D.R.m),
    (((D.hc τ).b ⟨i + 1, h⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) = LevelStarExponents.h0 L
  Ch_ge : max (768 * cThree * cSix) (2304 * cOne) ≤ Q.ChT
  primes : 6 * (D.R.k : ℝ) / D.R.m ≤ D.host.q / Real.log D.host.q ∧
    6 * (D.R.k : ℝ) / D.R.m ≤ D.host.d / Real.log D.host.d
  height_ge_node_count : ((Q.TO : ℝ) + dY D + 2) * (2 * ((Q.TO : ℝ) + dY D + 2) + 2 * D.R.r + Q.nP) + Q.nP +
    2 * ((Q.TO : ℝ) + dY D + 2) + 2 * D.R.r + 2 ≤ LevelStarExponents.h0 L - D.R.r
  w_poly : max (384 * cThree * cSix) (1152 * cOne) * D.R.r * (D.R.f : ℝ) ^ 2 * D.R.m * (D.R.k : ℝ) ^ 2 * dY D *
      Q.TO * Q.PP ≤ L.sc.b ^ (9 / 10 : ℝ) ∧ L.sc.b ^ (9 / 10 : ℝ) ≤ L.sc.w'' D.R.n
  share : 385 * Q.PP * D.R.f * D.R.k * Real.exp (-L.sc.x ^ (L.sc.ez / 7)) ≤ 1

theorem Choice.x_ge_eps {Q : ParamsT D L P} {j : ℕ} (h : Choice Q j) :
    2 * L.sc.x ^ (L.sc.ez / 7) ≤ L.sc.x ^ (L.sc.eps / 6) ∧
      2 * (L.Ct + 4) * Real.log L.sc.x + 6 ≤ L.sc.x ^ ((L.sc.eps : ℝ) / 6) := by
  have h1 : L.sc.x ^ (L.sc.ez / 6) ≤ L.sc.x ^ (L.sc.eps / 6) :=
    Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by linarith [L.sc.ez_le])
  exact ⟨h.x_ge.1.trans h1, h.x_ge.2.trans h1⟩

end Run

def ParamStatement : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (Q : ParamsT D L P) (j : ℕ), 1 ≤ j → j ≤ D.R.m → Choice Q j →
    ∀ N : OT.Num, Reading Q j N → OT.Dom Q.CP N → ParamLines Q j N ∧ DelStrong D L j N

end GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

end
