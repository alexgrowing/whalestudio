import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly

namespace UpperTheory.V.ZK.TorsionExponentBound

theorem exponent_le (e n N m D : ℝ) (he : 1 ≤ e) (hn : 1 ≤ n) (hN1 : 1 ≤ N) (hN : N ≤ 4 * e + 6)
    (hm : m ≤ 2 * e + 1) (hD : 1 ≤ D) :
    12 * (m + 1) * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + (m + 1) * (2 * (n * N * N)) + 2 * m ≤
      (2 * e * n) ^ 24 * Real.log (2 * D) := by
  have hD2 : (0 : ℝ) < 2 * D := by linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL2 : Real.log 2 ≤ Real.log (2 * D) := Real.log_le_log (by norm_num) (by linarith)
  have hL : (0.69 : ℝ) < Real.log (2 * D) := by linarith
  have ha1 : 1 ≤ e * n := by nlinarith
  have hea : e ≤ e * n := by nlinarith
  have hP1 : 1 ≤ n * N := by nlinarith
  have hP : n * N ≤ 10 * (e * n) := by nlinarith
  have hNa : N ≤ 10 * (e * n) := by linarith
  have hm1 : m + 1 ≤ 4 * (e * n) := by linarith
  have hlogP : Real.log (2 * D * (n * N)) ≤ 16 * (e * n) * Real.log (2 * D) := by
    rw [Real.log_mul (ne_of_gt hD2) (ne_of_gt (by linarith))]
    have := Real.log_le_sub_one_of_pos (show 0 < n * N by linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 hL.le) (by linarith : (0 : ℝ) ≤ 16 * (e * n) - 1)]
  have hlogP0 : 0 ≤ Real.log (2 * D * (n * N)) := Real.log_nonneg (by nlinarith)
  have hA0 : 0 ≤ 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N) := by
    have : 0 ≤ n * N := by linarith
    positivity
  have hA : 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N) ≤
      1920300 * (e * n) ^ 5 * Real.log (2 * D) := by
    have h3 : (n * N) ^ 3 ≤ (10 * (e * n)) ^ 3 := pow_le_pow_left₀ (by linarith) hP 3
    have t1 : 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) ≤
        12 * (10 * (e * n)) ^ 3 * (10 * (e * n)) * (16 * (e * n) * Real.log (2 * D)) := by
      have : 0 ≤ (n * N) ^ 3 := by positivity
      have : 0 ≤ N := by linarith
      gcongr
    have t2 : 2 * (n * N * N) ≤ 300 * (e * n) ^ 5 * Real.log (2 * D) := by
      have q1 : n * N * N ≤ 10 * (e * n) * (10 * (e * n)) := by
        apply mul_le_mul hP hNa (by linarith) (by linarith)
      have q2 : (e * n) ^ 2 ≤ (e * n) ^ 5 := pow_le_pow_right₀ ha1 (by norm_num)
      have q3 : 0 ≤ (e * n) ^ 5 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hL.le q3]
    have q4 : 0 ≤ Real.log (2 * D) := by linarith
    nlinarith [t1, t2]
  have hE : (2 * e * n) ^ 24 = 2 ^ 24 * (e * n) ^ 24 := by ring
  have hp6 : (e * n) ^ 6 ≤ (e * n) ^ 24 := pow_le_pow_right₀ ha1 (by norm_num)
  have hp1 : e * n ≤ (e * n) ^ 6 := by
    calc e * n = (e * n) ^ 1 := (pow_one _).symm
      _ ≤ (e * n) ^ 6 := pow_le_pow_right₀ ha1 (by norm_num)
  have hLpos : 0 ≤ Real.log (2 * D) := by linarith
  have k1 : (m + 1) * (12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N)) ≤
      4 * (e * n) * (1920300 * (e * n) ^ 5 * Real.log (2 * D)) := by
    calc _ ≤ 4 * (e * n) * (12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N)) :=
          mul_le_mul_of_nonneg_right hm1 hA0
      _ ≤ _ := mul_le_mul_of_nonneg_left hA (by linarith)
  have k2 : 2 * m ≤ 12 * (e * n) ^ 6 * Real.log (2 * D) := by
    nlinarith [mul_le_mul_of_nonneg_right hp1 hLpos]
  have k3 : (e * n) ^ 6 * Real.log (2 * D) ≤ (e * n) ^ 24 * Real.log (2 * D) :=
    mul_le_mul_of_nonneg_right hp6 hLpos
  rw [hE]
  have k4 : 4 * (e * n) * (1920300 * (e * n) ^ 5 * Real.log (2 * D)) =
      7681200 * ((e * n) ^ 6 * Real.log (2 * D)) := by ring
  nlinarith [k1, k2, k3, k4]

end UpperTheory.V.ZK.TorsionExponentBound

open NumberField UpperTheory.V

namespace UpperTheory.V.ZK

theorem torsAll : ∃ C : ℝ, ∀ (L) [Field L] [NumberField L], IsTotallyComplex L →
    ∀ e N m : ℕ, 1 ≤ e → 1 ≤ N → N ≤ 4 * e + 6 → m ≤ 2 * e + 1 →
      Finite (UpperTheory.V.K.torsHGL L N m) ∧
        Real.log (Nat.card (UpperTheory.V.K.torsHGL L N m)) ≤
          UpperTheory.V.kBound C e (Module.finrank ℚ L) (discr L).natAbs := by
  refine ⟨24, ?_⟩
  intro L _ _ hL e N m he hN1 hN hm
  haveI := hL
  have ht := UpperTheory.V.KT.tors_le L N m
  refine ⟨ht.1, ?_⟩
  have hn : 1 ≤ Module.finrank ℚ L := Module.finrank_pos
  have hD : 1 ≤ (discr L).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero L)
  have hdd : 1 ≤ Module.finrank ℚ L * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hA := UpperTheory.V.KT.orbnum L N m hN1
  have hBn : 0 < 2 * (discr L).natAbs * (Module.finrank ℚ L * N) := by positivity
  have hB : (0 : ℝ) < ((2 * (discr L).natAbs * (Module.finrank ℚ L * N) : ℕ) : ℝ) := by exact_mod_cast hBn
  have hAexp : ((UpperTheory.V.KT.orbBound L N m : ℕ) : ℝ) ≤
      Real.exp (12 * ((m : ℝ) + 1) * ((Module.finrank ℚ L : ℝ) * N) ^ 3 * N *
        Real.log (2 * ((discr L).natAbs : ℝ) * ((Module.finrank ℚ L : ℝ) * N))) := by
    have h1 : ((UpperTheory.V.KT.orbBound L N m : ℕ) : ℝ) ≤
        ((2 * (discr L).natAbs * (Module.finrank ℚ L * N) : ℕ) : ℝ) ^
          (12 * (m + 1) * (Module.finrank ℚ L * N) ^ 3 * N) := by exact_mod_cast hA
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hB] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have hsexp : (((3 ^ (UpperTheory.V.KT.dd L N * N) : ℕ)) : ℝ) ≤
      Real.exp (2 * ((Module.finrank ℚ L : ℝ) * N * N)) := by
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    push_cast
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    push_cast
    have : (0 : ℝ) ≤ (Module.finrank ℚ L : ℝ) * N * N := by positivity
    nlinarith
  have hs1 : 1 ≤ 3 ^ (UpperTheory.V.KT.dd L N * N) := Nat.one_le_pow _ _ (by norm_num)
  have key := ht.log_le_exp hs1 hAexp hsexp
  refine key.trans ?_
  unfold UpperTheory.V.kBound
  apply Real.exp_le_exp.2
  have hE := UpperTheory.V.ZK.TorsionExponentBound.exponent_le (e : ℝ) (Module.finrank ℚ L : ℝ) (N : ℝ) (m : ℝ)
    ((discr L).natAbs : ℝ) (by exact_mod_cast he) (by exact_mod_cast hn) (by exact_mod_cast hN1)
    (by exact_mod_cast hN) (by exact_mod_cast hm) (by exact_mod_cast hD)
  refine hE.trans (le_of_eq ?_)
  rw [show ((24 : ℝ)) = ((24 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

end UpperTheory.V.ZK

open NumberField UpperTheory.V in
theorem UpperTheory.V.ZK.sTors :
    UpperTheory.V.ZK.STors := by
  obtain ⟨C, h⟩ := UpperTheory.V.ZK.torsAll
  exact ⟨C, fun L _ _ hL E hE m hm => (h L hL E (4 * E + 6) m hE (by omega) le_rfl hm).2⟩
