import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.LeafMeans.LeafMeansFree

noncomputable section

open Finset

namespace IxMeans

structure MeansPack (Tau ι : Type) [Fintype Tau] [Fintype ι] where

  N : ℕ

  f : ℕ

  T : ℕ

  D : ℕ

  jp : ℕ

  m : ℕ

  nc : ℕ

  u : Tau → Fin N → ℝ

  u1 : Tau → Fin N → ℝ

  up : Tau → Fin N → ℝ

  c0 : ℝ

  b : ℝ

  rd : ℝ

  x : ℝ

  Lp : ℝ

  h0 : ℝ

  fourthRootConstant : ℝ

  sl : ι → ℝ

  e : ℕ →₀ ℝ

  SB : Finset ℕ

  cpp : ℕ → ℝ

  vdd : ℕ → ℝ

  Pinf : ℝ

  PPe : ℝ

  XW : ℝ

def C7 : ℝ := 40

def Cn : ℝ := 2

def Ce : ℝ := 200

namespace MeansPack

variable {Tau ι : Type} [Fintype Tau] [Fintype ι] (P : MeansPack Tau ι)

def nrm (v : Tau → Fin P.N → ℝ) : ℝ := ∑ τ, ∑ i, |v τ i|
def U : ℝ := P.nrm P.u
def U1 : ℝ := P.nrm P.u1
def Up : ℝ := P.nrm P.up

def spread : ℝ := ∑ τ, ((⨆ i, P.up τ i) - ⨅ i, P.up τ i)
def E0 : ℝ := (P.f : ℝ) * P.N * (P.c0 + 4 * P.N)
def L : ℝ := Real.log P.b
def LL0 : ℝ := Real.log (P.b * P.rd) * Real.log (Real.log P.x) + |P.Lp| + Real.log P.x
def indexMeanConstant : ℝ := 100 + 9 * |P.fourthRootConstant|
def CT2 : ℝ := 7 + (|P.fourthRootConstant + Real.log (2 * Real.pi)| + 3 / 2) / Real.log 128
def X : ℝ := P.indexMeanConstant * P.LL0 * P.Up
def H : ℝ := (⨆ τ, ⨆ i, |P.up τ i|) / (P.h0 / (4 * P.T))
def B0 : ℝ := 4 * P.f * (P.N : ℝ) ^ 2 * (1 + P.H)
def Pa : ℝ := 9 / 2 * P.f * P.N * P.m + 3 / 2 * P.f * (P.N : ℝ) ^ 2 + 6 * Cn * P.f * P.m * (P.nc + 1)
def ap (p : ℕ) : ℝ := if p ∈ P.SB then (P.cpp p + C7 * P.vdd p) * (P.Up + P.Pa) else 0
def cinf : ℝ := (1 * P.U1 + 6 * P.Pinf) / 2
def Sp : Finset ℕ := P.e.support ∪ P.SB
def cc : ℝ := ∑ p ∈ P.Sp, (P.e p + P.ap p) * Real.log p + P.cinf
def Qcc : ℝ := P.PPe + P.XW + 104 * P.L * P.Pa + 3 * P.Pinf
def mean : ℝ := (∑ c, P.sl c) / (Fintype.card ι : ℝ)

def IntermediateScaleBounds : Prop := ((P.T : ℝ) + P.D + 1) * P.U1 ≤ P.U + P.E0 ∧ P.Up ≤ P.U1

def HeightGapBound : Prop := P.H ≤ 8 * P.b / P.h0

def SpreadBoundVariant : Prop := (P.jp : ℝ) * P.spread ≤ 6 * P.Up

def I6 : Prop := ∑ p ∈ P.e.support, P.e p * Real.log p ≤ Ce * P.LL0 * P.U1 + P.PPe + P.XW

def I7 : Prop := -(P.CT2 * ((Real.log (P.B0 * P.rd) + |P.Lp|) * P.Up + P.jp * P.spread)) ≤ P.mean

def PrimeSum : Prop := ∑ p ∈ P.SB, (P.cpp p + C7 * P.vdd p) * Real.log p ≤ 104 * P.L

end MeansPack

structure Rows {Tau ι : Type} [Fintype Tau] [Fintype ι] (P : MeansPack Tau ι) : Prop where
  hb : 0 < P.b
  hL : 1 ≤ P.L
  hrd : 1 ≤ P.rd
  hx : 1 ≤ P.x
  hllx : 1 ≤ Real.log (Real.log P.x)
  hf : 1 ≤ P.f
  hN : 1 ≤ P.N
  hh0 : 32 * (P.f : ℝ) * (P.N : ℝ) ^ 2 ≤ P.h0
  hSZ2 : 4 * (P.f : ℝ) * (P.N : ℝ) ^ 2 ≤ P.b

namespace MeansPack

variable {Tau ι : Type} [Fintype Tau] [Fintype ι] (P : MeansPack Tau ι)

theorem nrm_nonneg (v : Tau → Fin P.N → ℝ) : 0 ≤ P.nrm v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem log_scale_lower_bounds (h : Rows P) :
    P.L ≤ P.LL0 ∧ 1 ≤ P.LL0 ∧ 1 < Real.log P.x ∧ 0 ≤ Real.log (P.b * P.rd) := by
  have hrd := h.hrd
  have hbr : Real.log (P.b * P.rd) = P.L + Real.log P.rd := by
    unfold L; rw [Real.log_mul h.hb.ne' (by linarith)]
  have hlrd : 0 ≤ Real.log P.rd := Real.log_nonneg hrd
  have hlx0 : 0 ≤ Real.log P.x := Real.log_nonneg h.hx
  have hlx1 : 1 < Real.log P.x := by
    by_contra hc
    push_neg at hc
    have : Real.log (Real.log P.x) ≤ 0 := Real.log_nonpos hlx0 hc
    linarith [h.hllx]
  have hL := h.hL
  have hbr0 : 0 ≤ Real.log (P.b * P.rd) := by rw [hbr]; linarith
  have h1 : Real.log (P.b * P.rd) ≤ Real.log (P.b * P.rd) * Real.log (Real.log P.x) := by
    nlinarith [h.hllx]
  have hab := abs_nonneg P.Lp
  refine ⟨?_, ?_, hlx1, hbr0⟩
  · unfold LL0; linarith
  · unfold LL0; linarith

theorem H_nonneg (h : Rows P) : 0 ≤ P.H := by
  have hf : (1 : ℝ) ≤ P.f := by exact_mod_cast h.hf
  have hN : (1 : ℝ) ≤ P.N := by exact_mod_cast h.hN
  have h0 : 0 < P.h0 := by nlinarith [h.hh0]
  unfold H
  apply div_nonneg
  · exact Real.iSup_nonneg fun τ => Real.iSup_nonneg fun i => abs_nonneg _
  · exact div_nonneg h0.le (by positivity)

theorem B0_pos_and_le_two_mul_b (h : Rows P) (hd : P.HeightGapBound) : 0 < P.B0 ∧ P.B0 ≤ 2 * P.b := by
  have hH := P.H_nonneg h
  have hf : (1 : ℝ) ≤ P.f := by exact_mod_cast h.hf
  have hN : (1 : ℝ) ≤ P.N := by exact_mod_cast h.hN
  have hN2 : (1 : ℝ) ≤ (P.N : ℝ) ^ 2 := by nlinarith
  have hK : 0 < 4 * (P.f : ℝ) * (P.N : ℝ) ^ 2 := by nlinarith
  have h0 : 0 < P.h0 := by nlinarith [h.hh0]
  have hb := h.hb
  constructor
  · unfold B0; exact mul_pos hK (by linarith)
  · have k1 : 4 * (P.f : ℝ) * (P.N : ℝ) ^ 2 * P.H ≤ 4 * (P.f : ℝ) * (P.N : ℝ) ^ 2 * (8 * P.b / P.h0) :=
      mul_le_mul_of_nonneg_left hd hK.le
    have k2 : 4 * (P.f : ℝ) * (P.N : ℝ) ^ 2 * (8 * P.b / P.h0) ≤ P.b := by
      have e : 4 * (P.f : ℝ) * (P.N : ℝ) ^ 2 * (8 * P.b / P.h0) = (32 * (P.f : ℝ) * (P.N : ℝ) ^ 2 * P.b) / P.h0 := by
        ring
      rw [e, div_le_iff₀ h0]
      nlinarith [h.hh0]
    have hS := h.hSZ2
    unfold B0
    nlinarith

theorem second_time_constant_bounds : 0 ≤ P.CT2 ∧ 8 * P.CT2 ≤ P.indexMeanConstant := by
  have h2 := Real.log_two_gt_d9
  have h128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  have ht : (9 / 2 : ℝ) ≤ Real.log 128 := by rw [h128]; linarith
  have hpi := Real.pi_le_four
  have hpi3 := Real.pi_gt_three
  have hl0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  have hl1 : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have habs : |P.fourthRootConstant + Real.log (2 * Real.pi)| ≤ |P.fourthRootConstant| + 7 := by
    have := abs_add_le P.fourthRootConstant (Real.log (2 * Real.pi))
    rw [abs_of_nonneg hl0] at this
    linarith
  have hA0 : 0 ≤ |P.fourthRootConstant + Real.log (2 * Real.pi)| + 3 / 2 := by positivity
  have hq0 : 0 ≤ (|P.fourthRootConstant + Real.log (2 * Real.pi)| + 3 / 2) / Real.log 128 := div_nonneg hA0 (by linarith)
  have hqm : (|P.fourthRootConstant + Real.log (2 * Real.pi)| + 3 / 2) / Real.log 128 * Real.log 128 =
      |P.fourthRootConstant + Real.log (2 * Real.pi)| + 3 / 2 := div_mul_cancel₀ _ (by linarith)
  have hq1 : 9 / 2 * ((|P.fourthRootConstant + Real.log (2 * Real.pi)| + 3 / 2) / Real.log 128) ≤
      |P.fourthRootConstant + Real.log (2 * Real.pi)| + 3 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left ht hq0]
  have hr := abs_nonneg P.fourthRootConstant
  unfold CT2 indexMeanConstant
  constructor
  · linarith
  · linarith

theorem X_nonneg (h : Rows P) : 0 ≤ P.X := by
  obtain ⟨_, hLL1, _, _⟩ := P.log_scale_lower_bounds h
  unfold X indexMeanConstant
  exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (P.nrm_nonneg _)

theorem log_height_le_twice_log_scale (h : Rows P) (hd : P.HeightGapBound) : Real.log (P.B0 * P.rd) + |P.Lp| ≤ 2 * P.LL0 := by
  obtain ⟨hB0, hB2⟩ := P.B0_pos_and_le_two_mul_b h hd
  obtain ⟨_, _, hlx, hbr0⟩ := P.log_scale_lower_bounds h
  have hrd := h.hrd
  have hb := h.hb
  have h1 : Real.log (P.B0 * P.rd) ≤ Real.log (2 * P.b * P.rd) :=
    Real.log_le_log (mul_pos hB0 (by linarith)) (mul_le_mul_of_nonneg_right hB2 (by linarith))
  have h2 : Real.log (2 * P.b * P.rd) = Real.log 2 + Real.log (P.b * P.rd) := by
    rw [mul_assoc, Real.log_mul (by norm_num) (mul_pos hb (by linarith)).ne']
  have h3 := Real.log_two_lt_d9
  have h4 : Real.log (P.b * P.rd) ≤ Real.log (P.b * P.rd) * Real.log (Real.log P.x) := by
    nlinarith [h.hllx]
  have hab := abs_nonneg P.Lp
  unfold LL0
  linarith

theorem means_b (h : Rows P) (hd : P.HeightGapBound) (he : P.SpreadBoundVariant) (h7 : P.I7) : -P.X ≤ P.mean := by
  have hlog := P.log_height_le_twice_log_scale h hd
  obtain ⟨_, hLL1, _, _⟩ := P.log_scale_lower_bounds h
  obtain ⟨hC0, hC8⟩ := P.second_time_constant_bounds
  have hUp : 0 ≤ P.Up := P.nrm_nonneg _
  have e1 : (Real.log (P.B0 * P.rd) + |P.Lp|) * P.Up ≤ 2 * P.LL0 * P.Up :=
    mul_le_mul_of_nonneg_right hlog hUp
  have e0 : 1 * P.Up ≤ P.LL0 * P.Up := mul_le_mul_of_nonneg_right hLL1 hUp
  have e2 : (P.jp : ℝ) * P.spread ≤ 6 * P.LL0 * P.Up := by
    unfold SpreadBoundVariant at he; linarith
  have e3 : P.CT2 * ((Real.log (P.B0 * P.rd) + |P.Lp|) * P.Up + P.jp * P.spread) ≤
      P.CT2 * (8 * P.LL0 * P.Up) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0
  have hLU : 0 ≤ P.LL0 * P.Up := mul_nonneg (by linarith) hUp
  have e4 : 8 * P.CT2 * (P.LL0 * P.Up) ≤ P.indexMeanConstant * (P.LL0 * P.Up) := mul_le_mul_of_nonneg_right hC8 hLU
  unfold I7 at h7
  unfold X
  linarith

theorem sum_e : ∑ p ∈ P.Sp, P.e p * Real.log p = ∑ p ∈ P.e.support, P.e p * Real.log p := by
  symm
  apply Finset.sum_subset (fun p hp => Finset.mem_union_left _ hp)
  intro p _ hp
  have : P.e p = 0 := by
    by_contra hne
    exact hp (Finsupp.mem_support_iff.mpr hne)
  rw [this, zero_mul]

theorem sum_a : ∑ p ∈ P.Sp, P.ap p * Real.log p =
    (P.Up + P.Pa) * ∑ p ∈ P.SB, (P.cpp p + C7 * P.vdd p) * Real.log p := by
  have h1 : ∑ p ∈ P.SB, P.ap p * Real.log p = ∑ p ∈ P.Sp, P.ap p * Real.log p := by
    apply Finset.sum_subset (fun p hp => Finset.mem_union_right _ hp)
    intro p _ hp
    simp only [ap, if_neg hp, zero_mul]
  rw [← h1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [ap, if_pos hp]
  ring

theorem cc_eq : P.cc = ∑ p ∈ P.e.support, P.e p * Real.log p +
    (P.Up + P.Pa) * ∑ p ∈ P.SB, (P.cpp p + C7 * P.vdd p) * Real.log p + P.cinf := by
  rw [← P.sum_e, ← P.sum_a, ← Finset.sum_add_distrib]
  unfold cc
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem means_a (h : Rows P) (ha : P.IntermediateScaleBounds) (h6 : P.I6) (hp : P.PrimeSum) :
    (P.T : ℝ) * P.cc ≤ (Ce + 105) * P.LL0 * (P.U + P.E0) + P.T * P.Qcc := by
  obtain ⟨hLL, hLL1, _, _⟩ := P.log_scale_lower_bounds h
  have hL := h.hL
  have hT : (0 : ℝ) ≤ P.T := Nat.cast_nonneg _
  have hD : (0 : ℝ) ≤ P.D := Nat.cast_nonneg _
  have hU1 : 0 ≤ P.U1 := P.nrm_nonneg _
  have hUp : 0 ≤ P.Up := P.nrm_nonneg _
  have hPa : 0 ≤ P.Pa := by unfold Pa Cn; positivity
  obtain ⟨ha1, ha2⟩ := ha
  have hDU : 0 ≤ ((P.D : ℝ) + 1) * P.U1 := mul_nonneg (by linarith) hU1
  have tU1 : (P.T : ℝ) * P.U1 ≤ P.U + P.E0 := by nlinarith
  have tUp : (P.T : ℝ) * P.Up ≤ P.U + P.E0 := by nlinarith [mul_le_mul_of_nonneg_left ha2 hT]
  have hA : 0 ≤ P.U + P.E0 := by nlinarith [mul_nonneg hT hU1]
  rw [P.cc_eq]
  unfold I6 at h6
  unfold PrimeSum at hp
  have hCe : (0 : ℝ) ≤ Ce * P.LL0 := by unfold Ce; linarith
  have k1 := mul_le_mul_of_nonneg_left h6 hT
  have k2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ P.Up + P.Pa)) hT
  have k3 : Ce * P.LL0 * (P.T * P.U1) ≤ Ce * P.LL0 * (P.U + P.E0) := mul_le_mul_of_nonneg_left tU1 hCe
  have k4 : 104 * P.L * (P.T * P.Up) ≤ 104 * P.L * (P.U + P.E0) := mul_le_mul_of_nonneg_left tUp (by linarith)
  have k5 : (104 * P.L + 1 / 2) * (P.U + P.E0) ≤ 105 * P.LL0 * (P.U + P.E0) :=
    mul_le_mul_of_nonneg_right (by linarith) hA
  unfold cinf Qcc
  linarith

theorem means_d (h : Rows P) (ha : P.IntermediateScaleBounds) {Ca : ℝ} (hCa : P.indexMeanConstant ≤ Ca) :
    (P.T : ℝ) * P.X ≤ Ca * P.LL0 * (P.U + P.E0) := by
  obtain ⟨_, hLL1, _, _⟩ := P.log_scale_lower_bounds h
  have hT : (0 : ℝ) ≤ P.T := Nat.cast_nonneg _
  have hD : (0 : ℝ) ≤ P.D := Nat.cast_nonneg _
  have hU1 : 0 ≤ P.U1 := P.nrm_nonneg _
  obtain ⟨ha1, ha2⟩ := ha
  have hDU : 0 ≤ ((P.D : ℝ) + 1) * P.U1 := mul_nonneg (by linarith) hU1
  have tUp : (P.T : ℝ) * P.Up ≤ P.U + P.E0 := by nlinarith [mul_le_mul_of_nonneg_left ha2 hT]
  have hA : 0 ≤ P.U + P.E0 := by nlinarith [mul_nonneg hT hU1]
  have hCI : 0 ≤ P.indexMeanConstant * P.LL0 := by unfold indexMeanConstant; exact mul_nonneg (by positivity) (by linarith)
  have k1 : P.indexMeanConstant * P.LL0 * (P.T * P.Up) ≤ P.indexMeanConstant * P.LL0 * (P.U + P.E0) := mul_le_mul_of_nonneg_left tUp hCI
  have k2 : P.indexMeanConstant * (P.LL0 * (P.U + P.E0)) ≤ Ca * (P.LL0 * (P.U + P.E0)) :=
    mul_le_mul_of_nonneg_right hCa (mul_nonneg (by linarith) hA)
  unfold X
  linarith

theorem means (h : Rows P) (ha : P.IntermediateScaleBounds) (hd : P.HeightGapBound) (he : P.SpreadBoundVariant) (h6 : P.I6) (hp : P.PrimeSum) (h7 : P.I7)
    {Ca Cb : ℝ} (hCa : P.indexMeanConstant ≤ Ca) (hCb : Ce + 105 ≤ Cb) :
    Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts.SlopeMeansBounds P.X P.sl (P.T : ℝ) P.LL0 P.U P.E0 P.cc P.Qcc Ca Cb := by
  obtain ⟨_, hLL1, _, _⟩ := P.log_scale_lower_bounds h
  have hT : (0 : ℝ) ≤ P.T := Nat.cast_nonneg _
  have hD : (0 : ℝ) ≤ P.D := Nat.cast_nonneg _
  have hU1 : 0 ≤ P.U1 := P.nrm_nonneg _
  have hA : 0 ≤ P.U + P.E0 := by
    obtain ⟨ha1, _⟩ := ha
    nlinarith [mul_nonneg hT hU1, mul_nonneg (by linarith : (0:ℝ) ≤ P.D + 1) hU1]
  refine ⟨P.X_nonneg h, ?_, P.means_d h ha hCa, ?_⟩
  · exact P.means_b h hd he h7
  · have k := P.means_a h ha h6 hp
    have k2 : (Ce + 105) * (P.LL0 * (P.U + P.E0)) ≤ Cb * (P.LL0 * (P.U + P.E0)) :=
      mul_le_mul_of_nonneg_right hCb (mul_nonneg (by linarith) hA)
    linarith

end MeansPack

end IxMeans
