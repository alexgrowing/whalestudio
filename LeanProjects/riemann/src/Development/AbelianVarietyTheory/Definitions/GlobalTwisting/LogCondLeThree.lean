import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.GlobalTheoryTheory NumberField

def NormOne (d M p : ℕ) : Prop := ∃ π : ℤ × ℤ, π.1 ^ 2 + (d : ℤ) * π.2 ^ 2 = 4 * (p : ℤ) ∧ Arith.CongOne M π

def ModRow (s : Scale) (N d : ℕ) : Prop :=
  d.Prime ∧ d % 4 = 3 ∧ 100 ≤ d ∧ 0 < N ∧ d ∣ N ∧ Real.log N ≤ 3 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2

theorem modRow_host {s : Scale} {R : Ranks} (H : Host R)
    (h : Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 3 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) : ModRow s H.condN H.d := by
  have hd : H.d % 16 = 7 := H.hyp.2.2.2.1
  have h1 := H.qd_big.2
  have h2 := R.rank_add_five_le
  have h3 := R.m_add_three_le_k
  have h4 := R.two_le_m
  have hr : 6 ≤ R.r := by unfold Ranks.r; omega
  have ht : 11 ≤ R.t := by omega
  have h5 : 4 * 11 * 6 ≤ 4 * R.t * R.r := by gcongr
  refine ⟨H.hyp.2.1, by omega, by omega, H.condN_pos, Dvd.intro_left _ rfl, ?_⟩
  simpa [Formalism.HC.HostRaw.condN] using h

theorem HostVal.log_cond_le_three {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H) :
    Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 3 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  have h0 : 0 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _) (sq_nonneg _)
  have := h.log_cond_le
  nlinarith

theorem HostVal.modRow {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H) : ModRow s H.condN H.d :=
  modRow_host H h.log_cond_le_three

theorem modRow_of_rowq {s : Scale} {Y : ℝ} {n q d : ℕ} (hY : PairWin s Y) (hn : 1 ≤ n) (hd : 100 ≤ d)
    (h : Rowq Y s.eps n q d) : ModRow s (4 * n * q * d) d := by
  obtain ⟨hq, -, -, -, hd', hd16, -, -, -, -, hN⟩ := h
  have h0 : 0 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _) (sq_nonneg _)
  have h1 := hY.z_log_sq_le
  have hq0 := hq.pos
  refine ⟨hd', by omega, hd, by positivity, Dvd.intro_left _ rfl, ?_⟩
  push_cast
  nlinarith

def RealBox {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsCharE χ → GlobalTheoryTheory.IsRealChar χ → (H.q ∣ N ∨ H.d ∣ N) →
    ∀ β : ℝ, 1 - 1 / 400 < β → β < 1 → DirichletCharacter.LFunction χ β ≠ 0

theorem BoxH.realBox {R : Ranks} {H : Host R} {Y eps : ℝ} (h : BoxH H Y eps) : RealBox H.toHostRaw :=
  fun _ _ χ hχ hr hN β hβ _ => h.real_ne_zero χ ((isCharH_iff H χ).2 hχ) hr hN β hβ

theorem BoxW.realBox {s : Scale} {R : Ranks} {H : Host R} (h : BoxW s H) : RealBox H.toHostRaw :=
  fun _ _ χ hχ hr hN β hβ _ => h.real_ne_zero χ hχ hr hN β hβ

def QDChoice : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ C5 x0 : ℝ, 0 < C5 ∧ ∀ x ≥ x0, ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * x ^ (2 + 8 * eps) →
    ∃ q d : ℕ, Rowq x eps n q d ∧ QDq x eps C5 q d ∧ Boxq x eps q d

def ThinChoice : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ c : ℝ, 0 < c ∧ ∀ Co : ℝ, ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R),
    s.eps = eps → x0 ≤ s.x → RankVal s R → (R.o : ℝ) ≤ Co → (H.QS : ℝ) ≤ Co * R.n →
    Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 3 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 → RealBox H.toHostRaw → ThinOK s c H

open Classical in

def NormPrimes : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (N d : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R →
    ModRow s N d →
    (((R.k : ℝ) * s.b) ^ 8) ^ ((9 : ℝ) / 10) ≤ (((Finset.range (⌊2 * ((R.k : ℝ) * s.b) ^ 8⌋₊ + 1)).filter (fun g : ℕ =>
      g.Prime ∧ ((R.k : ℝ) * s.b) ^ 8 ≤ (g : ℝ) ∧ NormOne d N g)).card : ℝ)

def LevelPrime : Prop :=
  ∀ eps c : ℝ, 0 < eps → eps < 1 / 52 → 0 < c → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (N d g0 g1 : ℕ) (Ts : ℝ), s.eps = eps →
    x0 ≤ s.x → RankVal s R → ModRow s N d → 1 ≤ g0 → 1 ≤ g1 → (g0 : ℝ) ≤ s.b ^ 9 → (g1 : ℝ) ≤ s.b ^ 9 → 0 < Ts →
    c * R.m * s.L ≤ Real.log Ts →
    ∃ T : ℕ, T.Prime ∧ Ts ≤ (T : ℝ) ∧ (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * Ts ∧ NormOne d (N * (g0 * g1) ^ 2) T

def SmallPrimeOne : Prop := ∃ A : ℝ, 1 ≤ A ∧ ∀ M : ℕ, 2 ≤ M → ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (M : ℝ) ^ A

def TopsChoice : Prop :=
  ∀ eps Co : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x0 : ℝ, 0 < Cb ∧ ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x →
    RankVal s R → s.J ≤ Co → (R.o : ℝ) ≤ Co → ⌊s.x ^ (s.ez / 5)⌋₊ ≤ H.splitBound →
    ∃ TT : Finset (R.A), s.delta1 * R.n / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * s.delta1 * R.n ∧
      BadOK s Cb { H with TT := TT } ∧ R.toFrame.Shares TT (s.x ^ (-1 + s.eps))

open Classical in

def ShareMean : Prop :=
  ∀ eps C8 : ℝ, 0 < eps → eps < 1 / 52 → ∃ K0 : TransportedAlt, ∀ C : FC, Std C → C.Large K0 C.P.CF → ∀ cD ch : ℝ, 0 ≤ cD → ∃ x0 : ℝ,
    ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x → RankVal s R → HostVal s C8 H →
      ∀ W : Finset ((R.A → ℤ) × (R.A → ℤ)),
        (∀ w, w ∈ W ↔ (∀ t, t ∉ H.TT → w.1 t = 0 ∧ w.2 t = 0) ∧ WinOK s C.GK H w.1 w.2) →
        ∀ p, Arith.Loc.Cand (baseOf s cD ch H) C.GK (hPH H p) p →
          ∑ w ∈ W, Arith.Loc.Sig (baseOf s cD ch H) (Arith.ins (baseOf s cD ch H) C.GK 1) C.GK w.1 w.2 (hPH H p) p ≤
            (W.card : ℝ) * ((R.m : ℝ) * H.TT.card * s.x ^ (-12 : ℝ))

end GlobalTheory.EX

end
