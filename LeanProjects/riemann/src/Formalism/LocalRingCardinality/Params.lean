import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd

namespace Formalism.BasicNotions

structure Ranks extends Formalism.HC.Frame where
  k : ℕ
  m : ℕ
  t : ℕ
  k_even : Even k
  m_even : Even m
  t_odd : Odd t
  two_le_m : 2 ≤ m
  m_add_three_le_k : m + 3 ≤ k

  rank_add_five_le : k + m - 1 + 5 ≤ t
  three_m_lt_t : 3 * m < t

  m_le_f : m ≤ 2 * ord
  f_le_k : 2 * ord ≤ k

  m_sq_le_N : m ^ 2 ≤ k + m * (t + 1)

namespace Ranks

variable (R : Ranks)

def n : ℕ := R.ord

def f : ℕ := 2 * R.n

def r : ℕ := R.k + R.m - 1

def nV : ℕ := R.r + R.t

def N (j : ℕ) : ℕ := R.k + j * (R.t + 1)

def rS : ℕ := R.m / 2 - 1

def rankY (j : ℕ) : ℕ := R.r + j * R.t

def rankX' : ℕ := R.r + R.m * R.t

def sigY0 : ℕ × ℕ := (R.k + R.rS, R.rS + 1)

def sigW (j : ℕ) : ℕ × ℕ := (R.k + j - 1, R.m - j)

end Ranks

structure HCParam (R : Ranks) where
  u : Fin R.k → ℚ
  v : Fin (R.k - 1) → ℚ
  b : Fin R.m → ℚ
  e : Fin R.m → ℚ

  u_gt_v : ∀ i : Fin (R.k - 1), v i < u ⟨i.1, by omega⟩
  v_gt_u : ∀ i : Fin (R.k - 1), u ⟨i.1 + 1, by omega⟩ < v i

  u_last_gt : ∀ (h : 0 < R.k) (h' : 0 < R.m), -b ⟨0, h'⟩ < u ⟨R.k - 1, by omega⟩

  gap_be : ∀ j : Fin R.m, ((R.t : ℚ) + 3) / 2 ≤ e j - b j

  gap_eb : ∀ j : Fin R.m, ∀ h : j.1 + 1 < R.m, ((R.t : ℚ) + 3) / 2 ≤ b ⟨j.1 + 1, h⟩ - e j

  e_int : ∀ j : Fin R.m, ∃ z : ℤ, e j = z

  u_half : ∀ i : Fin R.k, ∃ z : ℤ, u i = z + 1 / 2
  v_int : ∀ i : Fin (R.k - 1), ∃ z : ℤ, v i = z
  b_int : ∀ j : Fin R.m, ∃ z : ℤ, b j = z

def sExp (R : Ranks) (ej : ℚ) (j : ℕ) : ℚ := ej - (R.N (j - 1) : ℚ) / 2

def sExp' (R : Ranks) (ej : ℚ) (j : ℕ) : ℚ := ej - (R.N j : ℚ) / 2

def wG (R : Ranks) (ej : ℚ) (j : ℕ) : ℚ := ej - (R.k : ℚ) / 2 - (2 * (j : ℚ) - 1) * ((R.t : ℚ) + 1) / 2

def RankBaseSpaceEq : Prop := ∀ R : Ranks, R.N 0 + 1 + 2 * R.rS = R.r

def SignatureBaseSpaceSum : Prop := ∀ R : Ranks, R.sigY0.1 + R.sigY0.2 = R.r

def FactSigW : Prop := ∀ R : Ranks, ∀ j, 1 ≤ j → j ≤ R.m → (R.sigW j).1 + (R.sigW j).2 = R.r

def SignatureBaseMiddleEq : Prop := ∀ R : Ranks, R.sigY0 = R.sigW (R.m / 2)

def FactWmDef : Prop := ∀ R : Ranks, (R.sigW R.m).2 = 0 ∧ (R.sigW R.m).1 = R.r

def FactXm : Prop := ∀ R : Ranks, R.N R.m = R.rankX' + 1

def FactYm : Prop := ∀ R : Ranks, R.rankY R.m = R.rankX'

def FactNStep : Prop := ∀ R : Ranks, ∀ j, R.N (j + 1) = R.N j + (R.t + 1)

def FactNEven : Prop := ∀ R : Ranks, ∀ j, Even (R.N j)

def FactROdd : Prop := ∀ R : Ranks, Odd R.r

def FactSigmaCount : Prop := ∀ R : Ranks, (R.k - 1) + R.m = R.r

def FactSShift : Prop := ∀ R : Ranks, ∀ (ej : ℚ) (j : ℕ), 1 ≤ j →
  sExp R ej j - sExp' R ej j = ((R.t : ℚ) + 1) / 2

def FactWG : Prop := ∀ R : Ranks, ∀ (ej : ℚ) (j : ℕ), 1 ≤ j →
  wG R ej j = sExp R ej j - (j : ℚ) * ((R.t : ℚ) + 1) / 2

def FactSInt : Prop := ∀ R : Ranks, ∀ (z : ℤ) (j : ℕ), 1 ≤ j →
  (∃ a : ℤ, sExp R (z : ℚ) j = a) ∧ (∃ a : ℤ, sExp' R (z : ℚ) j = a)

def FactNV : Prop := ∀ R : Ranks, R.nV - R.r = R.t

def FactHCMono : Prop := ∀ (R : Ranks) (P : HCParam R),
  (∀ i : Fin (R.k - 1), P.v i < P.u ⟨i.1, by omega⟩ ∧ P.u ⟨i.1 + 1, by omega⟩ < P.v i) ∧
  (∀ (h : 0 < R.k) (h' : 0 < R.m), -P.b ⟨0, h'⟩ < P.u ⟨R.k - 1, by omega⟩) ∧
  (∀ j : Fin R.m, -P.e j < -P.b j) ∧
  (∀ j : Fin R.m, ∀ h : j.1 + 1 < R.m, -P.b ⟨j.1 + 1, h⟩ < -P.e j)

theorem factHCMono : FactHCMono := by
  intro R P
  have ht : (0 : ℚ) ≤ R.t := by positivity
  refine ⟨fun i => ⟨P.u_gt_v i, P.v_gt_u i⟩, P.u_last_gt, fun j => ?_, fun j h => ?_⟩
  · have := P.gap_be j
    linarith
  · have := P.gap_eb j h
    linarith

end Formalism.BasicNotions
