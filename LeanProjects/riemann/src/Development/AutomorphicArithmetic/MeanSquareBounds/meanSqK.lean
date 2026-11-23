import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.MeanSquareBounds.twistK
import Development.AutomorphicArithmetic.MeanSquareBounds.SumMinLeDiv
import Development.AutomorphicArithmetic.MeanSquareBounds.SPsqLe
import Development.AutomorphicArithmetic.MeanSquareBounds.RRLe
import Development.AutomorphicArithmetic.MeanSquareBounds.SumCNLe
import Development.AutomorphicArithmetic.MeanSquareBounds.MeanSqAbs

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private lemma ev_log (δ A : ℝ) (hδ : 0 < δ) (hA : 0 < A) :
    ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, A * Real.log Y ≤ Y ^ δ := by
  have h := (isLittleO_log_rpow_atTop hδ).bound (c := 1 / A) (by positivity)
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 h
  refine ⟨max Y₀ 1, fun Y hY => ?_⟩
  have h1 := hY₀ Y (le_of_max_le_left hY)
  have hY1 : 1 ≤ Y := le_of_max_le_right hY
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hY1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at h1
  calc A * Real.log Y ≤ A * (1 / A * Y ^ δ) := mul_le_mul_of_nonneg_left h1 hA.le
    _ = Y ^ δ := by field_simp

private lemma sizes (y w : ℝ) (hy : 1 ≤ y) (hw0 : 0 ≤ w) (hw : w ≤ y ^ (1 / 5 : ℝ)) :
    Real.log y ≤ 2 * Real.sqrt y ∧ w * Real.log y ≤ 4 * Real.sqrt y := by
  have hy0 : 0 < y := by linarith
  have key : ∀ a : ℝ, 0 < a → a * Real.log y ≤ y ^ a := by
    intro a ha
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 a)
    rw [Real.log_rpow hy0] at h
    linarith
  have hsq : Real.sqrt y = y ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow y
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  constructor
  · have := key (1 / 2) (by norm_num)
    rw [hsq]
    linarith
  · have h3 := key (3 / 10) (by norm_num)
    have h3' : Real.log y ≤ 10 / 3 * y ^ (3 / 10 : ℝ) := by linarith
    have hmul : y ^ (1 / 5 : ℝ) * y ^ (3 / 10 : ℝ) = Real.sqrt y := by
      rw [← Real.rpow_add hy0, hsq]
      norm_num
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    calc w * Real.log y ≤ y ^ (1 / 5 : ℝ) * (10 / 3 * y ^ (3 / 10 : ℝ)) :=
          mul_le_mul hw h3' hl (Real.rpow_nonneg hy0.le _)
      _ = 10 / 3 * Real.sqrt y := by rw [← hmul]; ring
      _ ≤ 4 * Real.sqrt y := by linarith

set_option maxHeartbeats 800000 in
theorem meanSqK :
    ∃ C : ℝ, 0 < C ∧ ∀ ε K : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ K → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m₀ a₀ : ℕ),
      admitted ε Y U m₀ a₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ Y ^ (ε / 5) ∨ (Y ^ K) ^ 400 < (p : ℝ)) →
      MeanSq C ((Y ^ K) ^ 400) (PPset m₀ a₀ U) (Set.Icc Y (Y ^ K)) := by
  obtain ⟨C1, hC1, hRR⟩ := RR_le
  obtain ⟨C2, hC2, hsP⟩ := exists_primePowerSum_le_mul_log
  obtain ⟨C3, hC3, hsPsq⟩ := sPsq_le
  obtain ⟨C4, hC4, hcN⟩ := sum_cN_le
  refine ⟨C3 + 25 * C1 ^ 2 + 4 * C2 ^ 2 + 20 * C1 * C2 + C4 ^ 2, by positivity, ?_⟩
  intro ε K hε hε1 hK
  obtain ⟨Y1, hY1⟩ := ev_log (ε / 6) (1600 * K) (by positivity) (by positivity)
  obtain ⟨Y2, hY2⟩ := ev_log (1 / 2) (400 * K) (by norm_num) (by positivity)
  obtain ⟨Y3, hY3⟩ := twistK ε (800 * K) (K + 1) hε (by positivity) (by positivity)
  refine ⟨max (max Y1 Y2) (max Y3 3), fun Y hY U m₀ a₀ hA hp => ?_⟩
  have hYa : Y1 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hYb : Y2 ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hYc : Y3 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY
  have hY3' : (3 : ℝ) ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hY
  have hY0 : 0 < Y := by linarith
  have hY1' : (1 : ℝ) ≤ Y := by linarith
  have hLY : 0 ≤ Real.log Y := Real.log_nonneg hY1'
  obtain ⟨nstar, hn⟩ := hY3 Y hYc U m₀ a₀ hA
  set Z := (Y ^ K) ^ 400 with hZ
  have hYK1 : 1 ≤ Y ^ K := Real.one_le_rpow hY1' (by linarith)
  have hYK : Y ≤ Y ^ K := by
    simpa using Real.rpow_le_rpow_of_exponent_le hY1' hK
  have hZY : Y ^ K ≤ Z := le_self_pow₀ hYK1 (by norm_num)
  have hZpos : 0 < Z := by linarith
  have hlogZ : Real.log Z = 400 * K * Real.log Y := by
    rw [hZ, Real.log_pow, Real.log_rpow hY0]; push_cast; ring
  have hZ2 : Z ^ 2 = Real.exp (800 * K * Real.log Y) := by
    have h : Real.log (Z ^ 2) = 800 * K * Real.log Y := by
      rw [Real.log_pow, hlogZ]; push_cast; ring
    rw [← h, Real.exp_log (pow_pos hZpos 2)]
  have hZ2' : Z ^ 2 = Y ^ (800 * K) := by
    rw [hZ2, Real.rpow_def_of_pos hY0]; ring_nf
  have hN : ((⌊Z⌋₊ : ℕ) : ℝ) ≤ Z := Nat.floor_le hZpos.le
  have hN2 : (((⌊Z⌋₊ ^ 2 : ℕ)) : ℝ) ≤ Z ^ 2 := by
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
  have hq : ∀ q ∈ Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ U, Nat.Prime q ∧ q % m₀ = a₀ % m₀ ∧ ⌊Z⌋₊ ^ 2 < q := by
    intro q hqP
    simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset, Finset.mem_filter, Finset.mem_Icc] at hqP
    obtain ⟨⟨hq1, hqU⟩, hqp, hqm, hqs⟩ := hqP
    refine ⟨hqp, hqm, ?_⟩
    have hUf : 0 < ⌊U⌋₊ := by omega
    have hU1 : 1 ≤ U := Nat.floor_pos.1 hUf
    have hU0 : 0 < U := by linarith
    have hlo := hA.lo
    have hy1 := hY1 Y hYa
    have h1 : Z ^ 2 ≤ U ^ (1 / 2 : ℝ) := by
      rw [hZ2, Real.rpow_def_of_pos hU0]
      apply Real.exp_le_exp.2
      linarith
    have h2 : (((⌊Z⌋₊ ^ 2 : ℕ)) : ℝ) < (q : ℝ) := by linarith
    exact_mod_cast h2
  have hs : ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → s ≤ ⌊Z⌋₊ ^ 2 → s ≠ nstar →
      |∑ q ∈ Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ U, ((jacobiSym (q : ℤ) s : ℤ) : ℝ)| ≤
        Y ^ (-(K + 1)) * ((Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ U).card : ℝ) := by
    intro s h1 h2 h3 h4 h5 h6
    apply hn s h1 h2 h3 h4 _ h6
    have : ((s : ℕ) : ℝ) ≤ (((⌊Z⌋₊ ^ 2 : ℕ)) : ℝ) := by exact_mod_cast h5
    rw [← hZ2']
    linarith
  set w := Y ^ (ε / 5) with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow hY1' (by positivity)
  have hpw : ∀ p : ℕ, Nat.Prime p → p ∣ m₀ → p ≤ ⌊Z⌋₊ → (p : ℝ) ≤ w := by
    intro p hpr hd hpN
    rcases hp p hpr hd with h | h
    · exact h
    · have : ((p : ℕ) : ℝ) ≤ ((⌊Z⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpN
      linarith
  have hη0 : 0 ≤ Y ^ (-(K + 1)) := Real.rpow_nonneg hY0.le _
  have hprod : Y ^ K * Y * Y ^ (-(K + 1)) = 1 := by
    rw [show Y ^ K * Y * Y ^ (-(K + 1)) = Y ^ (K + 1 + (-(K + 1))) by
      rw [Real.rpow_add hY0, Real.rpow_add hY0, Real.rpow_one]]
    simp
  intro y hy κ hκ
  obtain ⟨hYy, hyYK⟩ := hy
  have hy3 : (3 : ℝ) ≤ y := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hL1 : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hwy : w ≤ y ^ (1 / 5 : ℝ) := by
    calc w ≤ Y ^ (1 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1' (by linarith)
      _ ≤ y ^ (1 / 5 : ℝ) := Real.rpow_le_rpow hY0.le hYy (by norm_num)
  obtain ⟨hsz1, hsz2⟩ := sizes y w (by linarith) (by linarith) hwy
  have hmain := meanSq_abs (Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ U) m₀ a₀ nstar Z y (Y ^ (-(K + 1)))
    (C2 * Real.log y) κ hA.eight hA.coprime hy0 hη0 hq hκ (fun p => hsP y hy3 _ p) hs
  refine le_trans hmain ?_
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  set L := Real.log y with hLdef
  set R := RR (cN y) m₀ ⌊Z⌋₊ with hRdef
  set sq := Real.sqrt y with hsqdef
  have hL0 : 0 ≤ L := by linarith
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg y
  have hsq2 : sq * sq = y := Real.mul_self_sqrt hy0
  have hsq1 : 1 ≤ sq := Real.one_le_sqrt.2 (by linarith)
  have hsqy : sq ≤ y := by
    calc sq = sq * 1 := (mul_one sq).symm
      _ ≤ sq * sq := mul_le_mul_of_nonneg_left hsq1 hsq0
      _ = y := hsq2
  have hR0 : 0 ≤ R := by
    rw [hRdef, RR]
    exact Finset.sum_nonneg (fun n _ => cN_nonneg y hy0 n)
  have hRle : R ≤ 5 * C1 * sq := by
    have := hRR y hy3 ⌊Z⌋₊ m₀ w hw1 hpw
    calc R ≤ C1 * (sq + w * L) := this
      _ ≤ C1 * (5 * sq) := mul_le_mul_of_nonneg_left (by linarith) hC1.le
      _ = 5 * C1 * sq := by ring
  have hyL : y ≤ y * L := le_mul_of_one_le_right hy0 hL1
  have hA1 := hsPsq y hy3 ⌊Z⌋₊
  have hR2 : R ^ 2 ≤ 25 * C1 ^ 2 * (y * L) := by
    have h := pow_le_pow_left₀ hR0 hRle 2
    have h' : (5 * C1 * sq) ^ 2 = 25 * C1 ^ 2 * (sq * sq) := by ring
    have h3 : 25 * C1 ^ 2 * y ≤ 25 * C1 ^ 2 * (y * L) :=
      mul_le_mul_of_nonneg_left hyL (by positivity)
    rw [h', hsq2] at h
    linarith
  have hB2 : 2 * (C2 * L) ^ 2 ≤ 4 * C2 ^ 2 * (y * L) := by
    have hL2 : L ≤ 2 * y := by linarith
    have h1 : L * L ≤ 2 * y * L := mul_le_mul_of_nonneg_right hL2 hL0
    have h2 : C2 ^ 2 * (L * L) ≤ C2 ^ 2 * (2 * y * L) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    have h3 : 2 * (C2 * L) ^ 2 = 2 * (C2 ^ 2 * (L * L)) := by ring
    have h4 : 2 * (C2 ^ 2 * (2 * y * L)) = 4 * C2 ^ 2 * (y * L) := by ring
    linarith
  have hBR : 2 * (C2 * L) * R ≤ 20 * C1 * C2 * (y * L) := by
    have h1 : 2 * (C2 * L) * R ≤ 2 * (C2 * L) * (5 * C1 * sq) :=
      mul_le_mul_of_nonneg_left hRle (by positivity)
    have h2 : L * sq ≤ 2 * y := by
      have := mul_le_mul_of_nonneg_right hsz1 hsq0
      rw [mul_assoc, hsq2] at this
      exact this
    have h3 : C1 * C2 * (L * sq) ≤ C1 * C2 * (2 * y) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : C1 * C2 * y ≤ C1 * C2 * (y * L) := mul_le_mul_of_nonneg_left hyL (by positivity)
    have h5 : 2 * (C2 * L) * (5 * C1 * sq) = 10 * (C1 * C2 * (L * sq)) := by ring
    have h6 : C1 * C2 * (2 * y) = 2 * (C1 * C2 * y) := by ring
    have h7 : 20 * C1 * C2 * (y * L) = 20 * (C1 * C2 * (y * L)) := by ring
    linarith
  have hS0 : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, cN y n :=
    Finset.sum_nonneg (fun n _ => cN_nonneg y hy0 n)
  have hS : ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, cN y n ≤ C4 * y * (400 * K * Real.log Y) := by
    rw [← hlogZ]; exact hcN y Z hy0 (by linarith)
  have hKL : (400 * K * Real.log Y) ^ 2 ≤ Y := by
    have h := hY2 Y hYb
    have h0 : 0 ≤ 400 * K * Real.log Y := by positivity
    have h' := pow_le_pow_left₀ h0 h 2
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hY0.le] at h'
    exact h'
  have hS2 : (∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, cN y n) ^ 2 ≤ C4 ^ 2 * y ^ 2 * Y := by
    have h := pow_le_pow_left₀ hS0 hS 2
    have h2 : (C4 * y * (400 * K * Real.log Y)) ^ 2 ≤ C4 ^ 2 * y ^ 2 * Y := by
      rw [show (C4 * y * (400 * K * Real.log Y)) ^ 2 = C4 ^ 2 * y ^ 2 * (400 * K * Real.log Y) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left hKL (by positivity)
    linarith
  have hη1 : y * Y * Y ^ (-(K + 1)) ≤ 1 := by
    calc y * Y * Y ^ (-(K + 1)) ≤ Y ^ K * Y * Y ^ (-(K + 1)) := by gcongr
      _ = 1 := hprod
  have hηt : Y ^ (-(K + 1)) * (∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, cN y n) ^ 2 ≤ C4 ^ 2 * (y * L) := by
    calc Y ^ (-(K + 1)) * (∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, cN y n) ^ 2
        ≤ Y ^ (-(K + 1)) * (C4 ^ 2 * y ^ 2 * Y) := mul_le_mul_of_nonneg_left hS2 hη0
      _ = C4 ^ 2 * y * (y * Y * Y ^ (-(K + 1))) := by ring
      _ ≤ C4 ^ 2 * y * 1 := mul_le_mul_of_nonneg_left hη1 (by positivity)
      _ ≤ C4 ^ 2 * (y * L) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hyL (sq_nonneg _)
  have hA1' : ∑ p ∈ Finset.Icc 1 ⌊Z⌋₊ with Nat.Prime p, sP (cN y) ⌊Z⌋₊ p ^ 2 ≤ C3 * (y * L) := by
    have : C3 * y * L = C3 * (y * L) := by ring
    linarith
  calc _ ≤ C3 * (y * L) + 25 * C1 ^ 2 * (y * L) + 4 * C2 ^ 2 * (y * L) + 20 * C1 * C2 * (y * L)
        + C4 ^ 2 * (y * L) := by linarith
    _ = (C3 + 25 * C1 ^ 2 + 4 * C2 ^ 2 + 20 * C1 * C2 + C4 ^ 2) * y * L := by ring

end QH
