import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.InertJacobiLevels.HostFam

noncomputable section

namespace GlobalTheory.Mem.Num

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits

def evenCeil (y : ℝ) : ℕ := 2 * ⌈y / 2⌉₊

variable (C : FC) (s : Scale) (n : ℕ)

def eAt : ℕ := Nat.clog 2 ⌈s.x ^ (2 + 8 * s.eps)⌉₊

def nAt : ℕ := 2 ^ eAt s

def fAt : ℕ := 2 * n

def mAt : ℕ := evenCeil (Real.sqrt (s.x * s.delta1))

def kAt : ℕ := evenCeil (s.x ^ (9 / 2 + 10 * s.eps))

def rAt : ℕ := kAt s + mAt s - 1

def nWAt : ℕ := 8 * ⌈C.P.CnW * (rAt s : ℝ) * ((fAt n : ℝ) + (fAt n : ℝ) ^ 2 * ((kAt s : ℝ) - 1) ^ 3 * s.L ^ 2 / (mAt s : ℝ)) / 8⌉₊

def nPAt : ℕ := 8 * fAt n * rAt s + 4

def TOAt : ℕ := ⌈s.x ^ C.T.cTO⌉₊

def tAt : ℕ := TOAt C s * nWAt C s n + nPAt s n - rAt s

def NAt : ℕ := kAt s + mAt s * (tAt C s n + 1)

def PPAt : ℝ := C.T.CP * ((fAt n : ℝ) * (rAt s : ℝ) * s.L) ^ C.T.eP

def DpAt : ℕ := fAt n * (rAt s).choose 2

def RanksOK : Prop :=
  Odd (tAt C s n) ∧ 2 ≤ mAt s ∧ mAt s + 3 ≤ kAt s ∧ kAt s + mAt s - 1 + 5 ≤ tAt C s n ∧ 3 * mAt s < tAt C s n ∧
    mAt s ≤ 2 * n ∧ 2 * n ≤ kAt s ∧ mAt s ^ 2 ≤ kAt s + mAt s * (tAt C s n + 1)

def ranksOf (φ : Formalism.HC.Frame) (h : RanksOK C s φ.ord) : Ranks where
  toFrame := φ
  k := kAt s
  m := mAt s
  t := tAt C s φ.ord
  k_even := even_two_mul _
  m_even := even_two_mul _
  t_odd := h.1
  two_le_m := h.2.1
  m_add_three_le_k := h.2.2.1
  rank_add_five_le := h.2.2.2.1
  three_m_lt_t := h.2.2.2.2.1
  m_le_f := h.2.2.2.2.2.1
  f_le_k := h.2.2.2.2.2.2.1
  m_sq_le_N := h.2.2.2.2.2.2.2

def cStar : ℝ := max (max C.P.CDel C.P.CCount) (max C.P.Ch0N 7)

def cP : ℝ := 7 * C.T.eP - 1

def cDel : ℝ := (C.Ct + 5) * cStar C + cStar C * (C.P.CF + 6) + 2 * C.Ct + 10

def cLam : ℝ := max (3 * C.Ct + 6) (cDel C + 17) + 1

def cH : ℝ := max (max (max (cLam C + 1) ((C.Ct + 5) * cStar C)) (max (cStar C * (C.Ct + 1) + 6) (3 * C.Ct + 7)))
  (max (cP C + C.T.cTO + C.Ct + 30) 100)

def DelAt : ℕ := ⌈s.x ^ cDel C⌉₊

def hhAt : ℕ := ⌈s.x ^ cH C⌉₊

def etaAt : ℝ := (mAt s : ℝ) * (2 * (hhAt C s : ℝ))

def ScAt : ℝ := (kAt s : ℝ) * (4 * (DelAt C s : ℝ))

def j0At : ℕ := ⌈Real.logb 5 ((n : ℝ) * (NAt C s n : ℝ) / (mAt s : ℝ))⌉₊

def LwAt : ℕ := 10 * ⌈(C.Ct + 4) * Real.log s.x⌉₊ + 2 * ⌈30 / s.eps⌉₊ + 22

def GamAt : ℝ := Real.exp (C.CGam * (mAt s : ℝ) ^ 5 * (fAt n : ℝ) * s.L)

def wordsAt : ℕ := ⌈3 * GamAt C s n ^ 2 * s.x ^ C.P.CF⌉₊

def YAt : ℝ := ((kAt s : ℝ) * s.b) ^ 8

def bTopAt : ℝ := s.b' + 2 * (n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (kAt s : ℝ)

structure HCIn where
  Del : ℕ
  hh : ℕ
  B : ℤ
  U1 : ℤ
  Uk : ℤ
  δ : ℕ → Bool

def HCIn.OK (I : HCIn) (R : Ranks) : Prop :=
  1 ≤ I.Del ∧ R.t + 3 ≤ 2 * I.hh ∧ ((R.k : ℤ) - 2) * (4 * I.Del) ≤ I.U1 ∧ I.Uk ≤ -1 ∧ -I.B ≤ I.Uk

def HCIn.vZ (I : HCIn) (R : Ranks) (i : ℕ) : ℤ := ((R.k : ℤ) - 2 - i) * (4 * I.Del)

def HCIn.uZ (I : HCIn) (R : Ranks) (i : ℕ) : ℤ :=
  if i = 0 then I.U1 else if i + 1 = R.k then I.Uk
  else ((R.k : ℤ) - 1 - i) * (4 * I.Del) - 1 - (if I.δ (i - 1) then (I.Del : ℤ) else 0)

def HCIn.hc (I : HCIn) (R : Ranks) (h : I.OK R) : HCParam R where
  u i := (I.uZ R i : ℚ) + 1 / 2
  v i := (I.vZ R i : ℚ)
  b j := ((I.B + (j : ℕ) * (2 * I.hh) : ℤ) : ℚ)
  e j := ((I.B + (j : ℕ) * (2 * I.hh) + I.hh : ℤ) : ℚ)
  u_gt_v i := by
    obtain ⟨h1, -, h3, -, -⟩ := h
    have hi := i.2
    have h1' : (1 : ℤ) ≤ I.Del := by exact_mod_cast h1
    have : I.vZ R i ≤ I.uZ R i := by
      unfold HCIn.vZ HCIn.uZ
      split_ifs with a b c
      · rw [a]; simpa using h3
      · omega
      · nlinarith
      · nlinarith
    have h' : (I.vZ R i : ℚ) ≤ I.uZ R i := by exact_mod_cast this
    show (I.vZ R i : ℚ) < (I.uZ R i : ℚ) + 1 / 2
    linarith
  v_gt_u i := by
    obtain ⟨h1, -, -, h4, -⟩ := h
    have hi := i.2
    have h1' : (1 : ℤ) ≤ I.Del := by exact_mod_cast h1
    have : I.uZ R (i + 1) + 1 ≤ I.vZ R i := by
      unfold HCIn.vZ HCIn.uZ
      rw [if_neg (Nat.succ_ne_zero _)]
      split_ifs with b c
      · have : (R.k : ℤ) - 2 - (i : ℕ) = 0 := by omega
        rw [this]; omega
      · push_cast; nlinarith
      · push_cast; nlinarith
    have h' : (I.uZ R (i + 1) : ℚ) + 1 ≤ I.vZ R i := by exact_mod_cast this
    show (I.uZ R (i + 1) : ℚ) + 1 / 2 < (I.vZ R i : ℚ)
    linarith
  u_last_gt hk hm := by
    obtain ⟨-, -, -, -, h5⟩ := h
    have h3 := R.m_add_three_le_k
    have : I.uZ R (R.k - 1) = I.Uk := by
      unfold HCIn.uZ
      rw [if_neg (by omega), if_pos (by omega)]
    have h' : (-I.B : ℚ) ≤ I.Uk := by exact_mod_cast h5
    show -((I.B + (0 : ℕ) * (2 * I.hh) : ℤ) : ℚ) < (I.uZ R (R.k - 1) : ℚ) + 1 / 2
    rw [this]; push_cast; linarith
  gap_be j := by
    have h' : (R.t : ℚ) + 3 ≤ 2 * I.hh := by exact_mod_cast h.2.1
    push_cast; linarith
  gap_eb j hj := by
    have h' : (R.t : ℚ) + 3 ≤ 2 * I.hh := by exact_mod_cast h.2.1
    push_cast; linarith
  e_int j := ⟨_, rfl⟩
  u_half i := ⟨_, rfl⟩
  v_int i := ⟨_, rfl⟩
  b_int j := ⟨_, rfl⟩

section Places

variable {R : Ranks} (H : Host R) (a b : R.A → ℤ)

instance psiFin (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

open Classical in

def baseZ (g : R.GG) : ℤ :=
  if g ∈ H.topPlaces then b (R.iotaInv g.2) + ⌊s.b' / s.x⌋
  else if g ∈ H.thickPlaces then ⌈s.b⌉ else ⌈s.w'' R.n⌉

def shiftPl : R.GG := R.tau2 (R.dig (sInf (H.T2 : Set ℕ)) + H.u0)

open Classical in

def nodeZ (g : R.GG) : ℤ :=
  baseZ s H b g + if g = shiftPl H ∧ Odd (∑ g' : R.Psi, baseZ s H b (g' : R.GG)) then 1 else 0

open Classical in

def inAt (δ : ℕ → Bool) (g : R.GG) : HCIn where
  Del := DelAt C s
  hh := hhAt C s
  B := nodeZ s H b g
  U1 := if g ∈ H.topPlaces then a (R.iotaInv g.2) + (R.k / 2 : ℕ) - 1
    else ((R.k : ℤ) - 2) * (4 * DelAt C s) + R.k * (4 * DelAt C s)
  Uk := if g ∈ H.topPlaces then -b (R.iotaInv g.2) - (R.k / 2 : ℕ) else -1
  δ := δ

end Places

end GlobalTheory.Mem.Num

end
