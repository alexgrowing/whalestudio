import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.LocalRingCardinality.DataParams₂
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField

noncomputable section

namespace GlobalTheory.MeanTop

structure Wts (ι : Type) (N : ℕ) where

  kc : ℕ

  p : ℕ

  T : ℕ

  Dd : ℕ

  c0 : ℤ

  h0 : ℤ

  S : ℝ

  eta : ℝ

  b : ℝ

  w : ι → ℝ

  u : ι → Fin N → ℤ

  u1 : ι → Fin N → ℤ

namespace Wts

variable {ι : Type} {N : ℕ} (W : Wts ι N)

def u' : ι → Fin N → ℤ := fun τ i => if (i : ℕ) < W.p then W.u1 τ i else W.u1 τ i + 3 * (N : ℤ)

def g : ℝ := (W.h0 : ℝ) / (4 * W.T)

def IsDiv : Prop :=
  ∀ τ, (∀ a : Fin N, (a : ℕ) + 1 = W.kc → W.u1 τ a = 0) ∧ ∀ a b : Fin N, (b : ℕ) = a + 1 →
    W.u1 τ a - W.u1 τ b =
      (W.u τ a - W.u τ b + if (b : ℕ) = W.p then -W.c0 - (2 * (N : ℤ) - 2) else 2) / ((W.T : ℤ) + W.Dd + 1)

structure Hyp : Prop where
  kc_pos : 1 ≤ W.kc
  kc_lt : W.kc < W.p
  p_lt : W.p < N
  small : N - W.p < W.p
  weightConst_nonneg : 0 ≤ W.c0
  anchor : ∀ τ (a : Fin N), (a : ℕ) + 1 = W.kc → W.u τ a = 0
  h1 : 4 * W.Dd + 4 ≤ W.T
  h2 : 4 * (W.c0 + 2 * N + W.T + W.Dd + 1) ≤ W.h0 ∧ 24 * (N : ℤ) * W.T ≤ W.h0
  h3node : ∀ τ (a : Fin N), W.kc ≤ (a : ℕ) → |(W.u τ a : ℝ) + W.w τ| ≤ W.eta + W.S + N
  h3cloud : ∀ τ (a : Fin N), (a : ℕ) < W.kc → 0 ≤ W.u τ a ∧ (W.u τ a : ℝ) ≤ W.S
  h3w : ∀ τ, 4 * ((W.eta + W.S + N) + W.S + W.c0 + 2 * N) + 20 * N * W.T ≤ W.w τ
  h4 : ∀ τ (a b : Fin N), (b : ℕ) = a + 1 →
    ((b : ℕ) ≠ W.p → ((W.T : ℤ) + W.Dd + 2) * ((W.T : ℤ) + W.Dd + 2 + 2 * N) ≤ W.u τ a - W.u τ b + 2) ∧
    (W.kc ≤ (a : ℕ) → W.h0 - 1 ≤ W.u τ a - W.u τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ W.u τ a - W.u τ b)
  h5 : ∀ τ a, |(W.u τ a : ℝ)| + W.c0 + 4 * N ≤ 2 * W.b

end Wts

def l1 {ι : Type} [Fintype ι] {N : ℕ} (v : ι → Fin N → ℤ) : ℝ := ∑ τ, ∑ i, |(v τ i : ℝ)|

def ratWt {ι : Type} {N : ℕ} (v : ι → Fin N → ℤ) : ι → Fin N → ℚ := fun τ i => (v τ i : ℚ)

def reWt {ι : Type} {N : ℕ} (v : ι → Fin N → ℤ) : ι → Fin N → ℝ := fun τ i => (v τ i : ℝ)

def vDiff (D : D7) (p : ℕ) : ℝ := (padicValNat p (WeightThresholdDefs.dE D) : ℝ) / (Module.finrank ℚ D.host.E : ℝ)

structure Shifts where

  Pe : Finset ℕ

  e : ℕ → ℝ

  C7 : ℝ

  Pa : ℝ

  Pinf : ℝ

  PPe : ℝ

  XW : ℝ

variable {D : D7} (Y : ShimX D.what₂.Tau) {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters}

def bZero (W : Wts D.what₂.Tau Y.N) : ℝ := WeightThresholdDefs.bigB0 Y (reWt W.u') W.g

def totalShift (W : Wts D.what₂.Tau Y.N) (A : Shifts) : ℝ :=
  (∑ p ∈ A.Pe, A.e p * Real.log p) +
    (∑ p ∈ GlobalTheory.FlagAr.setB Y (bZero Y W), (WeightThresholdDefs.cP p + A.C7 * vDiff D p) * (l1 W.u' + A.Pa) * Real.log p) +
    (l1 W.u1 + 6 * A.Pinf) / 2

structure MeanTie (F : SlopeBoundLiftData K P) (W : Wts D.what₂.Tau Y.N) (A : Shifts) (CI : ℝ) : Prop where
  bar : W.p = Y.j
  dim : W.Dd = WeightThresholdDefs.dimY Y
  div : W.IsDiv
  len : F.T = W.T
  size : ∃ e : P.Pl ≃ D.what₂.Tau, ∀ τ, F.ua τ = ∑ i, |(W.u (e τ) i : ℝ)|
  slope : ∃ e : Y.Comp ≃ F.ι, GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.IsSlope Y (bZero Y W) (reWt W.u') (fun c => F.sl (e c))
  scale : P.b = W.b ∧ P.rd = D.host.rdE ∧ P.Lc = dlogL D 1 ∧ P.f = D.R.f ∧ Fintype.card D.what₂.Tau = D.R.f
  energyConstant_eq : F.E0 = P.f * Y.N * (W.c0 + 4 * Y.N)
  eX : F.X = CI * P.LL0 * l1 W.u'
  ecc : F.cc = totalShift Y W A
  eQ : F.Qcc = A.PPe + A.XW + 104 * P.L * A.Pa + 3 * A.Pinf

def MeanSizes (W : Wts D.what₂.Tau Y.N) (A : Shifts) : Prop :=
  W.Hyp ∧ 4 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 ≤ W.b ∧ 32 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 ≤ W.h0 ∧
    Y.lev.card ≤ 15 ∧ 0 ≤ A.C7 ∧ A.C7 ≤ 40 ∧ 0 ≤ A.Pa

def SumBound (P : SlopeBoundParameters) {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (A : Shifts) (Ce C2 : ℝ) : Prop :=
  (W.T : ℝ) * ∑ p ∈ A.Pe, A.e p * Real.log p ≤
    Ce * P.LL0 * (W.T * l1 W.u1) + W.T * (A.PPe + A.XW) + addY C2 P

def Shifts.Proper (A : Shifts) : Prop := ∀ p ∈ A.Pe, p.Prime ∧ 0 ≤ A.e p

structure LiftTie (F : SlopeBoundLiftData K P) (W : Wts D.what₂.Tau Y.N) : Prop where
  dimF : F.DY = W.Dd
  small : F.q' = Y.N - W.p
  diff : F.pq = (W.p : ℝ) - F.q'
  cloud : P.k = (W.kc : ℝ) + 1
  nodes : P.m = (Y.N : ℝ) - W.kc
  rank : P.Nr = Y.N
  width : P.S = W.S ∧ P.η = W.eta
  pos : ∃ e : P.Pl ≃ D.what₂.Tau, ∀ τ, F.w τ = W.w (e τ) ∧ F.ua τ = ∑ i, |(W.u (e τ) i : ℝ)|

end GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.Inhab

open Filter Topology

def wts (ι : Type) (N kc p T Dd c0 G V : ℕ) (b : ℝ) : Wts ι N where
  kc := kc
  p := p
  T := T
  Dd := Dd
  c0 := c0
  h0 := ((T : ℤ) + Dd + 1) * G - 1
  S := ((T : ℝ) + Dd + 1) * G * N
  eta := 2 * N + c0
  b := b
  w := fun _ => ((T : ℝ) + Dd + 1) * V
  u := fun _ i => (((T : ℤ) + Dd + 1) * G - 1) * ((kc : ℤ) - 1 - (i : ℕ)) -
    (if kc ≤ (i : ℕ) then ((T : ℤ) + Dd + 1) * V else 0) - (if p ≤ (i : ℕ) then 2 * (N : ℤ) + c0 else 0)
  u1 := fun _ i => (G : ℤ) * ((kc : ℤ) - 1 - (i : ℕ)) - (if kc ≤ (i : ℕ) then (V : ℤ) else 0)

theorem wts_isDiv (ι : Type) (N kc p T Dd c0 G V : ℕ) (b : ℝ) (hT : 1 ≤ T) :
    (wts ι N kc p T Dd c0 G V b).IsDiv := by
  intro τ
  refine ⟨fun a ha => ?_, fun a c hc => ?_⟩
  · simp only [wts] at ha ⊢
    have h1 : ¬ kc ≤ (a : ℕ) := by omega
    have h2 : (kc : ℤ) - 1 - (a : ℕ) = 0 := by omega
    simp [h1, h2]
  · have hc' : ((c : ℕ) : ℤ) = (a : ℕ) + 1 := by exact_mod_cast hc
    have key : ∀ x y : ℤ, y = 1 + ((T : ℤ) + Dd + 1) * x → x = y / ((T : ℤ) + Dd + 1) := by
      intro x y h
      rw [h, Int.add_mul_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt (by omega) (by omega)]; simp
    by_cases hp : (c : ℕ) = (wts ι N kc p T Dd c0 G V b).p
    · rw [if_pos hp]
      simp only [wts] at hp ⊢
      apply key
      rw [hc']
      split_ifs <;> first | (exfalso; omega) | ring1
    · rw [if_neg hp]
      simp only [wts] at hp ⊢
      apply key
      rw [hc']
      split_ifs <;> first | (exfalso; omega) | ring1

theorem wts_hyp (ι : Type) (N kc p T Dd c0 G V : ℕ) (b : ℝ) (h1 : 1 ≤ kc) (h2 : kc < p) (h3 : p < N) (h4 : N - p < p)
    (hT : 4 * Dd + 4 ≤ T) (hG1 : 4 * (c0 + 2 * N + T + Dd + 1) + 1 ≤ G) (hG2 : 24 * N * T + 1 ≤ G)
    (hG3 : (T + Dd + 2) * (T + Dd + 2 + 2 * N) ≤ G)
    (hV : 4 * ((2 * N + c0 + (T + Dd + 1) * G * N + N) + (T + Dd + 1) * G * N + c0 + 2 * N) + 20 * N * T ≤ V)
    (hb : (((T + Dd + 1) * G * N + (T + Dd + 1) * V + 6 * N + 2 * c0 : ℕ) : ℝ) ≤ 2 * b) :
    (wts ι N kc p T Dd c0 G V b).Hyp := by
  have hG0 : (1 : ℤ) ≤ G := by omega
  have hGM : (G : ℤ) ≤ ((T : ℤ) + Dd + 1) * G := by nlinarith [Int.natCast_nonneg T, Int.natCast_nonneg Dd]
  have hVM : (0 : ℤ) ≤ ((T : ℤ) + Dd + 1) * V := by positivity
  have hmain : ∀ a : Fin N, |(((T : ℤ) + Dd + 1) * G - 1) * ((kc : ℤ) - 1 - (a : ℕ))| ≤ ((T : ℤ) + Dd + 1) * G * N := by
    intro a
    have ha := a.isLt
    rw [abs_mul]
    apply mul_le_mul
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> omega
    · exact abs_nonneg _
    · linarith
  refine ⟨h1, h2, h3, h4, by simp [wts], ?_, hT, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ a ha
    simp only [wts] at ha ⊢
    have e1 : ¬ kc ≤ (a : ℕ) := by omega
    have e2 : ¬ p ≤ (a : ℕ) := by omega
    have e3 : (kc : ℤ) - 1 - (a : ℕ) = 0 := by omega
    simp [e1, e2, e3]
  · simp only [wts]; have : (4 * ((c0 : ℤ) + 2 * N + T + Dd + 1) + 1 ≤ G) := by exact_mod_cast hG1
    linarith
  · simp only [wts]; have : (24 * (N : ℤ) * T + 1 ≤ G) := by exact_mod_cast hG2
    linarith
  · intro τ a ha
    simp only [wts] at ha ⊢
    have hm := abs_le.mp (hmain a)
    have : |(((T : ℤ) + Dd + 1) * G - 1) * ((kc : ℤ) - 1 - (a : ℕ)) -
        (if kc ≤ (a : ℕ) then ((T : ℤ) + Dd + 1) * V else 0) - (if p ≤ (a : ℕ) then 2 * (N : ℤ) + c0 else 0) +
        ((T : ℤ) + Dd + 1) * V| ≤ 2 * N + c0 + ((T : ℤ) + Dd + 1) * G * N + N := by
      rw [if_pos ha, abs_le]
      have := Int.natCast_nonneg N
      have := Int.natCast_nonneg c0
      split_ifs <;> constructor <;> linarith [hm.1, hm.2]
    exact_mod_cast this
  · intro τ a ha
    simp only [wts] at ha ⊢
    have e1 : ¬ kc ≤ (a : ℕ) := by omega
    have e2 : ¬ p ≤ (a : ℕ) := by omega
    have hm := abs_le.mp (hmain a)
    simp only [if_neg e1, if_neg e2, sub_zero]
    refine ⟨mul_nonneg (by linarith) (by omega), ?_⟩
    exact_mod_cast hm.2
  · intro τ
    simp only [wts]
    have h : (4 * ((2 * N + c0 + (T + Dd + 1) * G * N + N) + (T + Dd + 1) * G * N + c0 + 2 * N) + 20 * N * T : ℝ) ≤ V := by
      exact_mod_cast hV
    have h' : (V : ℝ) ≤ ((T : ℝ) + Dd + 1) * V := by
      nlinarith [Nat.cast_nonneg (α := ℝ) T, Nat.cast_nonneg (α := ℝ) Dd, Nat.cast_nonneg (α := ℝ) V]
    push_cast
    linarith
  · intro τ a c hc
    simp only [wts]
    have hc' : ((c : ℕ) : ℤ) = (a : ℕ) + 1 := by exact_mod_cast hc
    have h : ((T : ℤ) + Dd + 2) * ((T : ℤ) + Dd + 2 + 2 * N) ≤ G := by exact_mod_cast hG3
    have := Int.natCast_nonneg N
    have := Int.natCast_nonneg c0
    rw [hc']
    have e : (((T : ℤ) + Dd + 1) * G - 1) * ((kc : ℤ) - 1 - (a : ℕ)) =
      (((T : ℤ) + Dd + 1) * G - 1) * ((kc : ℤ) - 1 - ((a : ℕ) + 1)) + (((T : ℤ) + Dd + 1) * G - 1) := by ring
    rw [e]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;> split_ifs <;> first | (exfalso; omega) | linarith
  · intro τ a
    simp only [wts]
    have hm := abs_le.mp (hmain a)
    have : |(((T : ℤ) + Dd + 1) * G - 1) * ((kc : ℤ) - 1 - (a : ℕ)) -
        (if kc ≤ (a : ℕ) then ((T : ℤ) + Dd + 1) * V else 0) - (if p ≤ (a : ℕ) then 2 * (N : ℤ) + c0 else 0)| + c0 + 4 * N
        ≤ ((T : ℤ) + Dd + 1) * G * N + ((T : ℤ) + Dd + 1) * V + 6 * N + 2 * c0 := by
      have := Int.natCast_nonneg N
      have := Int.natCast_nonneg c0
      have : |(((T : ℤ) + Dd + 1) * G - 1) * ((kc : ℤ) - 1 - (a : ℕ)) -
        (if kc ≤ (a : ℕ) then ((T : ℤ) + Dd + 1) * V else 0) - (if p ≤ (a : ℕ) then 2 * (N : ℤ) + c0 else 0)|
        ≤ ((T : ℤ) + Dd + 1) * G * N + ((T : ℤ) + Dd + 1) * V + 2 * N + c0 := by
        rw [abs_le]
        split_ifs <;> constructor <;> linarith [hm.1, hm.2]
      linarith
    have h2 : ((|(((T : ℤ) + Dd + 1) * G - 1) * ((kc : ℤ) - 1 - (a : ℕ)) -
        (if kc ≤ (a : ℕ) then ((T : ℤ) + Dd + 1) * V else 0) - (if p ≤ (a : ℕ) then 2 * (N : ℤ) + c0 else 0)| + c0 + 4 * N : ℤ) : ℝ)
        ≤ ((((T : ℤ) + Dd + 1) * G * N + ((T : ℤ) + Dd + 1) * V + 6 * N + 2 * c0 : ℤ) : ℝ) := by exact_mod_cast this
    rw [Int.cast_add, Int.cast_add, Int.cast_abs] at h2
    push_cast at h2 hb ⊢
    linarith

theorem exists_wts (ι : Type) (N kc p T Dd c0 Hb : ℕ) (h1 : 1 ≤ kc) (h2 : kc < p) (h3 : p < N) (h4 : N - p < p)
    (hT : 4 * Dd + 4 ≤ T) : ∃ b0 : ℝ, ∀ b, b0 ≤ b → ∃ W : Wts ι N, W.Hyp ∧ W.IsDiv ∧ W.kc = kc ∧ W.p = p ∧ W.T = T ∧
      W.Dd = Dd ∧ W.c0 = c0 ∧ W.b = b ∧ (Hb : ℤ) ≤ W.h0 ∧ 0 ≤ W.S ∧ ((kc : ℝ) + 1) * W.S ≤ b ∧
      ((kc : ℝ) + 1) * W.eta ≤ b := by
  obtain ⟨G, hG⟩ : ∃ G, G = 4 * (c0 + 2 * N + T + Dd + 1) + 1 + (24 * N * T + 1) + (T + Dd + 2) * (T + Dd + 2 + 2 * N) + Hb :=
    ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = 4 * ((2 * N + c0 + (T + Dd + 1) * G * N + N) + (T + Dd + 1) * G * N + c0 + 2 * N) + 20 * N * T :=
    ⟨_, rfl⟩
  have p1 : (0 : ℝ) ≤ (((T + Dd + 1) * G * N + (T + Dd + 1) * V + 6 * N + 2 * c0 : ℕ) : ℝ) := Nat.cast_nonneg _
  have p2 : (0 : ℝ) ≤ ((kc : ℝ) + 1) * (((T : ℝ) + Dd + 1) * G * N) := by positivity
  have p3 : (0 : ℝ) ≤ ((kc : ℝ) + 1) * (2 * (N : ℝ) + c0) := by positivity
  refine ⟨(((T + Dd + 1) * G * N + (T + Dd + 1) * V + 6 * N + 2 * c0 : ℕ) : ℝ) / 2 +
      ((kc : ℝ) + 1) * (((T : ℝ) + Dd + 1) * G * N) + ((kc : ℝ) + 1) * (2 * (N : ℝ) + c0), fun b hb =>
    ⟨wts ι N kc p T Dd c0 G V b, wts_hyp ι N kc p T Dd c0 G V b h1 h2 h3 h4 hT (by omega) (by omega) (by omega) hV.ge
      (by linarith), wts_isDiv ι N kc p T Dd c0 G V b (by omega), rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩⟩
  · show (Hb : ℤ) ≤ ((T : ℤ) + Dd + 1) * G - 1
    have : (Hb : ℤ) + 1 ≤ G := by omega
    nlinarith [Int.natCast_nonneg T, Int.natCast_nonneg Dd, Int.natCast_nonneg Hb]
  · show (0 : ℝ) ≤ ((T : ℝ) + Dd + 1) * G * N
    positivity
  · show ((kc : ℝ) + 1) * (((T : ℝ) + Dd + 1) * G * N) ≤ b
    linarith
  · show ((kc : ℝ) + 1) * (2 * (N : ℝ) + ((c0 : ℤ) : ℝ)) ≤ b
    push_cast
    linarith

example : (wts Unit 3 1 2 16 3 0 7 5 0).u1 () = ![0, -12, -19] ∧ (wts Unit 3 1 2 16 3 0 7 5 0).u' () = ![0, -12, -10] ∧
    (wts Unit 3 1 2 16 3 0 7 5 0).u () = ![0, -239, -384] := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp [wts, Wts.u']

theorem dividedWeight_unique {ι : Type} {N : ℕ} (W : Wts ι N) (v : ι → Fin N → ℤ) (hk : 1 ≤ W.kc) (hN : W.kc ≤ N) (h : W.IsDiv)
    (h' : Wts.IsDiv { W with u1 := v }) : v = W.u1 := by
  funext τ
  have step : ∀ a c : Fin N, (c : ℕ) = a + 1 → v τ a - W.u1 τ a = v τ c - W.u1 τ c := fun a c hc => by
    have e1 := (h τ).2 a c hc
    have e2 := (h' τ).2 a c hc
    simp only at e2
    omega
  have hN0 : 0 < N := by omega
  have all : ∀ n (hn : n < N), v τ ⟨n, hn⟩ - W.u1 τ ⟨n, hn⟩ = v τ ⟨0, hN0⟩ - W.u1 τ ⟨0, hN0⟩ := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih => intro hn; rw [← ih (by omega)]; exact (step ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl).symm
  have a1 := (h τ).1 ⟨W.kc - 1, by omega⟩ (by simp only; omega)
  have a2 := (h' τ).1 ⟨W.kc - 1, by omega⟩ (by simp only; omega)
  simp only at a2
  have a3 := all (W.kc - 1) (by omega)
  funext i
  have a4 := all i i.isLt
  simp only [Fin.eta] at a4
  omega

theorem chi_facts (D : D7) : (∀ n : ℕ, chiK D n = ((jacobiSym n D.host.d : ℤ) : ℂ)) ∧ (chiK D).IsPrimitive ∧ (chiK D).Odd := by
  have hp : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  have hd := D.host.hyp.2.2.2.1
  have hodd : (chiK D).Odd := by
    unfold DirichletCharacter.Odd chiK
    rw [MulChar.ringHomComp_apply, quadraticChar_neg_one (by rw [ZMod.ringChar_zmod_n]; omega), ZMod.card,
      ZMod.χ₄_nat_three_mod_four (by omega)]
    simp
  refine ⟨fun n => ?_, ?_, hodd⟩
  · unfold chiK
    rw [MulChar.ringHomComp_apply, ← jacobiSym.legendreSym.to_jacobiSym]
    simp [legendreSym]
  · have : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
    rw [DirichletCharacter.isPrimitive_def]
    rcases (Nat.Prime.eq_one_or_self_of_dvd D.host.hyp.2.1 _ (DirichletCharacter.conductor_dvd_level (chiK D))) with h | h
    · have h1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h
      unfold DirichletCharacter.Odd at hodd
      rw [h1, MulChar.one_apply (by simp)] at hodd
      norm_num at hodd
    · exact h

def page (D : D7) (N kc : ℕ) (x S η : ℝ) : SlopeBoundParameters :=
  { Pl := D.what₂.Tau, fPl := inferInstance, x := x, eps := 1, rd := D.host.rdE, v := D.host.rdE / 2, dN := D.host.d,
    dimNeZero := ⟨D.host.hyp.2.1.ne_zero⟩, χ := chiK D, Z := 0, logOmK := 0, logOm := 0, f := D.R.f, m := (N : ℝ) - kc,
    k := (kc : ℝ) + 1, S := S, η := η, R := 0, PPp := 20 * D.R.f * N ^ 2 * x, PPpp := 0, PP := 0,
    PPT := 5 * ((N : ℝ) - kc), Zpg := 0, nV := 0, Nr := N, g12 := 1 }

theorem f_pos (D : D7) : 1 ≤ D.R.f := by
  have := D.R.two_le_m
  have := D.R.m_le_f
  show 1 ≤ 2 * D.R.ord
  omega

theorem page_L (D : D7) (N kc : ℕ) (x S η : ℝ) : (page D N kc x S η).L = x := Real.rpow_one x

theorem page_b (D : D7) (N kc : ℕ) (x S η : ℝ) : (page D N kc x S η).b = Real.exp x := by
  unfold SlopeBoundParameters.b; rw [page_L]

theorem page_params (D : D7) (N kc : ℕ) (x S η : ℝ) (hrd : 4 ≤ D.host.rdE) (hx : 2187 ≤ x) (h1 : Real.log D.host.rdE ≤ x)
    (h2 : |dlogL D 1| ≤ x) (hk : kc < N) (hS0 : 0 ≤ S) (hS : ((kc : ℝ) + 1) * S ≤ Real.exp x)
    (hη : ((kc : ℝ) + 1) * η ≤ Real.exp x) : PageParams (page D N kc x S η) := by
  obtain ⟨c1, c2, c3⟩ := chi_facts D
  have hb : 0 < (page D N kc x S η).b := Real.exp_pos _
  have hL := page_L D N kc x S η
  refine ⟨c1, c2, c3, by show 1 ≤ x; linarith, by show (0 : ℝ) < 1; norm_num, hrd, by show 2 * (_ / 2) = D.host.rdE; ring,
    by show 0 < D.host.rdE / 2; linarith, by rw [hL]; exact h1, by rw [hL]; exact h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [page_b]; exact hS, by rw [page_b]; exact hη, hS0, le_rfl, ?_, ?_, ?_, ?_⟩
  · rw [hL]; show Real.log x ≤ x; linarith [Real.log_le_sub_one_of_pos (show 0 < x by linarith)]
  · show 1 ≤ Real.log (Real.log x)
    have e := Real.exp_one_lt_d9
    have e3 : Real.exp 3 ≤ x := by
      have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      have : Real.exp 1 ^ 3 ≤ 3 ^ 3 := by gcongr; linarith
      linarith
    have : 3 ≤ Real.log x := (Real.le_log_iff_exp_le (by linarith)).mpr e3
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith)
  · show 3 ≤ x ^ ((1 : ℝ) / 7)
    have : (3 : ℝ) = ((3 : ℝ) ^ (7 : ℕ)) ^ ((1 : ℝ) / 7) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this]
    exact Real.rpow_le_rpow (by norm_num) (by norm_num; exact hx) (by norm_num)
  · show ((Fintype.card D.what₂.Tau : ℕ) : ℝ) ≤ D.R.f
    rw [D.what₂.card_Tau]
  · show (1 : ℝ) ≤ (N : ℝ) - kc
    have : (kc : ℝ) + 1 ≤ N := by exact_mod_cast hk
    linarith
  · show (1 : ℝ) ≤ D.R.f
    exact_mod_cast f_pos D
  · show (1 : ℝ) ≤ (kc : ℝ) + 1
    linarith [Nat.cast_nonneg (α := ℝ) kc]
  · show ((kc : ℝ) + 1) * 0 ≤ _; linarith
  · rw [hL]; exact le_rfl
  · show (0 : ℝ) ≤ _; linarith
  · show (0 : ℝ) + 2 * 0 * 0 ≤ _; linarith

def fac {D : D7} (Y : ShimX D.what₂.Tau) (K : Type) [Field K] [NumberField K] [StarRing K] (x : ℝ)
    (W : Wts D.what₂.Tau Y.N) (A : Shifts) (CI : ℝ) (sl : Y.Comp → ℝ) : SlopeBoundLiftData K (page D Y.N W.kc x W.S W.eta) :=
  { w := W.w, w0 := W.w, c1 := fun _ => 0, ua := fun τ => ∑ i, |(W.u τ i : ℝ)|, kap := 1, q' := Y.N - W.p,
    pq := (W.p : ℝ) - (Y.N - W.p : ℕ), ι := Y.Comp, fι := inferInstance, nι := inferInstance, DY := W.Dd, A := 1, cs := 0,
    X := CI * (page D Y.N W.kc x W.S W.eta).LL0 * l1 W.u', cc := totalShift Y W A, E0 := D.R.f * Y.N * (W.c0 + 4 * Y.N),
    Qcc := A.PPe + A.XW + 104 * (page D Y.N W.kc x W.S W.eta).L * A.Pa + 3 * A.Pinf, ρ := 0,
    R1 := 0, R2 := 0, Bn := 1, δ' := 1, h := fun _ => 0, sl := sl, δc := fun _ => 1, dc := fun _ => 1,
    degc := fun _ => 0, PPf := 0, mv := 0, muU := 0, nA := 0, nB := 0, nN := 0, XA := fun _ => 1, XB := fun _ => 1,
    XN := fun _ => 1, LA := ⊥, LB := ⊥, NN := ⊥, Mk := ⊥, φ := 0, e := 0, g := 1, PPh := 0, abelian₂ := 0, δ := 0, o' := 0,
    n2 := 0 }

def shifts : Shifts := { Pe := {2}, e := fun _ => 1, C7 := 40, Pa := 1, Pinf := 1, PPe := Real.log 2, XW := 1 }

theorem shifts_proper : shifts.Proper := fun p hp => by
  obtain rfl : p = 2 := Finset.mem_singleton.mp hp
  exact ⟨Nat.prime_two, zero_le_one⟩

theorem joint {D : D7} (Y : ShimX D.what₂.Tau) (K : Type) [Field K] [NumberField K] [StarRing K] (kc c0 : ℕ) (CI Ce C2 : ℝ)
    (hCe : 0 ≤ Ce) (hC2 : 0 ≤ C2) (h1 : 1 ≤ kc) (h2 : kc < Y.j) (h3 : Y.N - Y.j < Y.j) (hrd : 4 ≤ D.host.rdE)
    (hbad : Y.lev.card ≤ 15)
    (sl : ℝ → (D.what₂.Tau → Fin Y.N → ℝ) → Y.Comp → ℝ) (hsl : ∀ B u, GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.IsSlope Y B u (sl B u)) :
    ∃ (P : SlopeBoundParameters) (F : SlopeBoundLiftData K P) (W : Wts D.what₂.Tau Y.N), W.kc = kc ∧ W.c0 = c0 ∧ PageParams P ∧ MeanTie Y F W shifts CI ∧
      LiftTie Y F W ∧ MeanSizes Y W shifts ∧ SumBound P W shifts Ce C2 ∧
      ∃ e : Y.Comp ≃ F.ι, ∀ c, F.sl (e c) = sl (bZero Y W) (reWt W.u') c := by
  have hj := Y.j_lt
  have hD : 1 ≤ WeightThresholdDefs.dimY Y := by
    show 1 ≤ Fintype.card D.what₂.Tau * (Y.N * (Y.N - 1) / 2)
    rw [D.what₂.card_Tau]
    have a : 3 * 2 ≤ Y.N * (Y.N - 1) := Nat.mul_le_mul (by omega) (by omega)
    exact Nat.mul_pos (f_pos D) (by omega)
  obtain ⟨n, hn⟩ : ∃ n, Y.N = kc + (n + 1) := ⟨Y.N - kc - 1, by omega⟩
  obtain ⟨b0, hW⟩ := exists_wts D.what₂.Tau Y.N kc Y.j (25 * WeightThresholdDefs.dimY Y ^ 2 * ((kc + 1) * (n + 1))) (WeightThresholdDefs.dimY Y) c0
    (32 * D.R.f * Y.N ^ 2) h1 h2 hj h3 (by
      have : 1 ≤ (kc + 1) * (n + 1) := Nat.mul_pos (by omega) (by omega)
      have h25 : 4 * WeightThresholdDefs.dimY Y + 4 ≤ 25 * WeightThresholdDefs.dimY Y ^ 2 := by nlinarith
      exact h25.trans (Nat.le_mul_of_pos_right _ this))
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 2187 + |Real.log D.host.rdE| + |dlogL D 1| + |b0| + 4 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 := ⟨_, rfl⟩
  have n1 := abs_nonneg (Real.log D.host.rdE)
  have n2 := abs_nonneg (dlogL D 1)
  have n3 := abs_nonneg b0
  have n4 : 0 ≤ 4 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 := by positivity
  have hb : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  obtain ⟨W, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12⟩ := hW (Real.exp x) (by linarith [le_abs_self b0])
  have hP : PageParams (page D Y.N W.kc x W.S W.eta) :=
    page_params D Y.N W.kc x W.S W.eta hrd (by linarith) (by linarith [le_abs_self (Real.log D.host.rdE)]) (by linarith)
      (by omega) w10 (by rw [w3]; exact w11) (by rw [w3]; exact w12)
  have hm : (Y.N : ℝ) - W.kc = (n : ℝ) + 1 := by
    rw [w3]
    have : (Y.N : ℝ) = kc + (n + 1) := by exact_mod_cast hn
    linarith
  refine ⟨page D Y.N W.kc x W.S W.eta, fac Y K x W shifts CI (sl (bZero Y W) (reWt W.u')), W, w3, w7, hP,
    ⟨w4, w6, w2, ?_, ⟨Equiv.refl _, fun _ => rfl⟩, ⟨Equiv.refl _, hsl _ _⟩,
      ⟨by rw [page_b, w8], rfl, rfl, rfl, D.what₂.card_Tau⟩, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩⟩,
    ⟨w1, by rw [w8]; linarith, by exact_mod_cast w9, hbad, by norm_num [shifts], by norm_num [shifts],
      by norm_num [shifts]⟩, ?_, Equiv.refl _, fun _ => rfl⟩
  · rw [w5]
    show ((⌈(5 * ((Y.N : ℝ) - W.kc)) ^ 2 * ((W.Dd : ℕ) : ℝ) ^ 2 * ((W.kc : ℝ) + 1) / ((Y.N : ℝ) - W.kc)⌉ : ℤ) : ℝ) = _
    have e : (5 * ((Y.N : ℝ) - W.kc)) ^ 2 * ((W.Dd : ℕ) : ℝ) ^ 2 * ((W.kc : ℝ) + 1) / ((Y.N : ℝ) - W.kc) =
        ((25 * WeightThresholdDefs.dimY Y ^ 2 * ((kc + 1) * (n + 1)) : ℕ) : ℝ) := by
      rw [hm, w3, w6]; push_cast; field_simp; ring
    rw [e, Int.ceil_natCast]; norm_cast
  · have hT : (0 : ℝ) ≤ W.T := Nat.cast_nonneg _
    have hl : 0 ≤ l1 W.u1 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hLL : 0 ≤ (page D Y.N W.kc x W.S W.eta).LL0 := by
      have a1 : 1 ≤ (page D Y.N W.kc x W.S W.eta).llx := hP.2.2.2.2.2.2.2.2.2.2.2.1
      have a2 : 0 ≤ Real.log ((page D Y.N W.kc x W.S W.eta).b * (page D Y.N W.kc x W.S W.eta).rd) := by
        rw [page_b]
        apply Real.log_nonneg
        show 1 ≤ Real.exp x * D.host.rdE
        nlinarith
      unfold SlopeBoundParameters.LL0
      exact add_nonneg (add_nonneg (mul_nonneg a2 (by linarith)) (abs_nonneg _)) hlx
    have hY : 0 ≤ addY C2 (page D Y.N W.kc x W.S W.eta) := by
      unfold addY
      rw [page_b]
      show 0 ≤ C2 * (D.R.f : ℝ) * ((Y.N : ℝ) - W.kc) * Real.exp x * Real.log x
      rw [hm]; positivity
    have hC : 0 ≤ Ce * (page D Y.N W.kc x W.S W.eta).LL0 * (W.T * l1 W.u1) := by positivity
    unfold SumBound shifts
    simp only [Finset.sum_singleton]
    push_cast
    nlinarith

def twoFlag (Tau : Type) [Fintype Tau] (N j : ℕ) (hj : 1 ≤ j) (hjN : j < N) : ShimX Tau where
  N := N
  j := j
  j_pos := hj
  j_lt := hjN
  lev := ∅
  lev_prime := by simp
  Comp := Bool
  vol := 2
  chern := (MvPolynomial.aeval (fun _ => (1 : ℝ))).toLinearMap ∘ₗ MvPolynomial.homogeneousComponent (Formalism.DegreeFormula.dimFl Tau N)
  chern_homog P d hd hP := by
    rw [LinearMap.comp_apply, MvPolynomial.homogeneousComponent_of_mem hP, if_neg hd.symm, map_zero]
  arDeg _ _ := 0
  arDeg_homog := by intros; rfl
  arMix _ _ _ := 0
  arMix_HT := by intros; rfl
  arMix_DR := by intros; rfl
  CurveHT _ := Unit
  degHT _ _ _ := 0
  CurveDR _ := Unit
  degDR _ _ _ := 0
  FibComp _ := Unit
  fibInBd _ _ := False
  Pt := Bool
  phiDR _ _ _ := 0
  phiMod _ _ _ := 0
  phiFr _ _ _ := 0
  XC := Bool
  rfn _ := Real.exp 1
  rfn_ge _ := le_rfl
  hLo _ := 1
  hUp _ := 1
  hLo_le _ := ⟨one_pos, le_rfl⟩
  connN _ := 0
  curvN _ := 0
  compOf := id
  normDetInf _ _ := 1
  compPt := id
  normDetT _ _ _ := 1
  normDetH _ _ _ := 1
  htDetT _ _ _ := 0
  ALB := ℝ
  arSelf L := ∑ c : Bool, (((Formalism.DegreeFormula.dimFl Tau N : ℕ) : ℝ) + 1) * ((if c then 1 else 0) + L)
  arSelfC L c := (((Formalism.DegreeFormula.dimFl Tau N : ℕ) : ℝ) + 1) * ((if c then 1 else 0) + L)
  arSelf_sum _ := rfl
  geo _ := ∑ _c : Bool, (1 : ℝ)
  geoC _ _ := 1
  geo_sum _ := rfl
  arVol L := L
  semipos _ := True
  nefFib _ := True
  arNef _ := True
  Mbar _ u s := (s : ℝ) - ∑ τ, ∑ i, |u τ i|

theorem twoFlag_isSlope (D : D7) (N j : ℕ) (hj : 1 ≤ j) (hjN : j < N) (B : ℝ) (u : D.what₂.Tau → Fin N → ℝ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.IsSlope (twoFlag D.what₂.Tau N j hj hjN) B u
      (fun c : Bool => (if c then 1 else 0) + (0 - ∑ τ, ∑ i, |u τ i|)) := by
  intro c
  have h : Tendsto (fun s : ℚ => (s : ℝ)) (𝓝[>] (0 : ℚ)) (𝓝 0) := by
    have := (Rat.continuous_coe_real.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  refine ((h.sub_const _).const_add _).congr fun s => ?_
  show _ = (((Formalism.DegreeFormula.dimFl D.what₂.Tau N : ℕ) : ℝ) + 1) * (_ + ((s : ℝ) - ∑ τ, ∑ i, |u τ i|)) / ((((Formalism.DegreeFormula.dimFl D.what₂.Tau N : ℕ) : ℝ) + 1) * 1)
  rw [mul_one, mul_div_cancel_left₀ _ (by positivity)]

theorem exists_joint (D : D7) (K : Type) [Field K] [NumberField K] [StarRing K] (N j kc c0 : ℕ) (CI Ce C2 : ℝ)
    (hCe : 0 ≤ Ce) (hC2 : 0 ≤ C2) (h1 : 1 ≤ kc) (h2 : kc < j) (hjN : j < N) (h3 : N - j < j) (hrd : 4 ≤ D.host.rdE) :
    ∃ (Y : ShimX D.what₂.Tau) (P : SlopeBoundParameters) (F : SlopeBoundLiftData K P) (W : Wts D.what₂.Tau Y.N) (A : Shifts),
      Y.N = N ∧ Y.j = j ∧ W.kc = kc ∧ W.c0 = c0 ∧ PageParams P ∧ MeanTie Y F W A CI ∧ LiftTie Y F W ∧ MeanSizes Y W A ∧
      SumBound P W A Ce C2 ∧ A.Proper ∧ (∃ p ∈ A.Pe, 0 < A.e p) ∧ 0 < A.C7 ∧ ∃ c c', F.sl c ≠ F.sl c' := by
  obtain ⟨P, F, W, a1, a2, a3, a4, a5, a6, a7, e, he⟩ :=
    joint (twoFlag D.what₂.Tau N j (by omega) hjN) K kc c0 CI Ce C2 hCe hC2 h1 h2 h3 hrd
      (by show (∅ : Finset ℕ).card ≤ 15; simp) _
      (twoFlag_isSlope D N j (by omega) hjN)
  refine ⟨_, P, F, W, shifts, rfl, rfl, a1, a2, a3, a4, a5, a6, a7, shifts_proper,
    ⟨2, Finset.mem_singleton_self 2, one_pos⟩, by norm_num [shifts], e true, e false, ?_⟩
  intro h
  have := (he true).symm.trans (h.trans (he false))
  simp at this

end GlobalTheory.MeanTop.Inhab
