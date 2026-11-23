import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeLower
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.BlockSizes
open Formalism.MainNotions.DIV.Inh (aPlusQ_anti aMinusQ_mono)

namespace GlobalTheory.BlockRows

theorem floor_cast_of_int {x : ℚ} (h : ∃ z : ℤ, x = z) (h1 : 1 ≤ x) : ((⌊x⌋₊ : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := h
  have hz : (0 : ℤ) ≤ z := by
    have : (1 : ℤ) ≤ z := by exact_mod_cast h1
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

theorem one_le_aPlusQ (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) : 1 ≤ DV.aPlusQ D j τ i := by
  have hk := D.R.m_add_three_le_k
  have hi : i.1 < D.R.k + j - 1 := i.2
  exact (DV.aPlusQ_last D j h1 h2 τ).trans
    (aPlusQ_anti D j τ (show i.1 ≤ D.R.k + j - 1 - 1 by omega) (by omega))

theorem one_le_aMinusQ (D : D7) (j : ℕ) (h1 : 1 ≤ j) (τ : D.what₂.Tau) (c : ℕ) (hc : j + c < D.R.m) :
    1 ≤ DV.aMinusQ D j τ c :=
  (DV.aMinusQ_last D j h1 (by omega) τ).trans (aMinusQ_mono D j τ (Nat.zero_le c) hc)

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  have := s.one_lt_alt
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)

theorem aPlus_le (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (L : SizeData₂ D)
    (hL : WindowsLe L) (i : Fin (D.R.sigW j).1) : DV.aPlus D j τ i ≤ 3 * L.sc.b ^ 2 := by
  have hk := D.R.m_add_three_le_k
  have hi : i.1 < D.R.k + j - 1 := i.2
  have h0 : 0 < D.R.k - 1 := by omega
  have a1 := aPlusQ_anti D j τ (Nat.zero_le i.1) (by omega)
  have hj : j - 1 < D.R.m := by omega
  have a2 : DV.aPlusQ D j τ 0 ≤ (D.hc τ).v ⟨0, h0⟩ + (D.hc τ).e ⟨j - 1, hj⟩ := by
    rw [DV.aPlusQ_eq]
    unfold DV.sigPar DV.eQ
    rw [dif_pos h0, dif_pos ⟨h1, h2⟩]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have hk' : (2 : ℚ) ≤ D.R.k := by exact_mod_cast (show 2 ≤ D.R.k by omega)
    have hj' : (0 : ℚ) ≤ j := Nat.cast_nonneg _
    push_cast
    linarith
  have a3 : DV.aPlus D j τ i ≤ (((D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) + (((D.hc τ).e ⟨j - 1, hj⟩ : ℚ) : ℝ) := by
    unfold DV.aPlus
    exact_mod_cast a1.trans a2
  have b1 := (L.cloud_v τ ⟨0, h0⟩).2
  have b2 := L.b_le τ ⟨j - 1, hj⟩
  have b3 := (abs_le.1 (L.be_close τ ⟨j - 1, hj⟩ ⟨j - 1, hj⟩)).1
  have b4 := one_le_b L.sc
  push_cast at b3
  have := hL.1
  have := hL.2
  nlinarith

theorem aMinus_le (D : D7) (j : ℕ) (h1 : 1 ≤ j) (τ : D.what₂.Tau) (L : SizeData₂ D)
    (hL : WindowsLe L) (c : ℕ) (hc : j + c < D.R.m) : DV.aMinus D j τ c ≤ 3 * L.sc.b ^ 2 := by
  have hj : j - 1 < D.R.m := by omega
  have a2 : DV.aMinusQ D j τ c ≤ (D.hc τ).b ⟨j + c, hc⟩ - (D.hc τ).e ⟨j - 1, hj⟩ := by
    unfold DV.aMinusQ DV.eQ
    rw [dif_pos hc, dif_pos ⟨h1, by omega⟩]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have hc' : (0 : ℚ) ≤ c := Nat.cast_nonneg _
    linarith
  have a3 : DV.aMinus D j τ c ≤ (((D.hc τ).b ⟨j + c, hc⟩ - (D.hc τ).e ⟨j - 1, hj⟩ : ℚ) : ℝ) := by
    unfold DV.aMinus
    exact_mod_cast a2
  have b3 := (abs_le.1 (L.be_close τ ⟨j + c, hc⟩ ⟨j - 1, hj⟩)).2
  have b4 := one_le_b L.sc
  have := hL.1
  nlinarith

theorem rows_sizes : ∀ (D : D7) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ τ : D.what₂.Tau, (Antitone (rowsP D j τ) ∧ (∀ i, 1 ≤ rowsP D j τ i) ∧ ∀ i, (rowsP D j τ i : ℝ) = DV.aPlus D j τ i) ∧ (Antitone (rowsM D j τ) ∧ (∀ i, 1 ≤ rowsM D j τ i) ∧ ∀ i, (rowsM D j τ i : ℝ) = DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i)) ∧ ∀ L : SizeData₂ D, WindowsLe L → (∀ i, (rowsP D j τ i : ℝ) ≤ 3 * L.sc.b ^ 2) ∧ ∀ i, (rowsM D j τ i : ℝ) ≤ 3 * L.sc.b ^ 2 := by
  intro D j h1 h2 τ
  have hk := D.R.m_add_three_le_k
  have hq : (D.R.sigW j).2 = D.R.m - j := rfl
  have hM : ∀ i : Fin (D.R.sigW j).2, j + ((D.R.sigW j).2 - 1 - i) < D.R.m := by
    intro i
    have := i.2
    omega
  have eP : ∀ i, (rowsP D j τ i : ℝ) = DV.aPlus D j τ i := by
    intro i
    have := floor_cast_of_int (DV.aPlusQ_int D j τ i) (one_le_aPlusQ D j h1 h2 τ i)
    unfold DV.aPlus rowsP
    rw [← this]
    simp
  have eM : ∀ i, (rowsM D j τ i : ℝ) = DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i) := by
    intro i
    have := floor_cast_of_int (DV.aMinusQ_int D j τ _) (one_le_aMinusQ D j h1 τ _ (hM i))
    unfold DV.aMinus rowsM
    rw [← this]
    simp
  refine ⟨⟨?_, ?_, eP⟩, ⟨?_, ?_, eM⟩, fun L hL => ⟨fun i => ?_, fun i => ?_⟩⟩
  · intro a b hab
    have hb : b.1 < D.R.k + j - 1 := b.2
    exact Nat.floor_le_floor (aPlusQ_anti D j τ (show a.1 ≤ b.1 from hab) (by omega))
  · intro i
    exact Nat.le_floor (by simpa using one_le_aPlusQ D j h1 h2 τ i)
  · intro a b hab
    have hab' : a.1 ≤ b.1 := hab
    exact Nat.floor_le_floor (aMinusQ_mono D j τ (by omega) (hM a))
  · intro i
    exact Nat.le_floor (by simpa using one_le_aMinusQ D j h1 τ _ (hM i))
  · rw [eP]
    exact aPlus_le D j h1 h2 τ L hL i
  · rw [eM]
    exact aMinus_le D j h1 τ L hL _ (hM i)

end GlobalTheory.BlockRows
