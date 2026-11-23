import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqSumEqSumSqAddTwoMulSumLt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZetaProdSphereVolumeBounds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NegLogProdLValEtaLeAndPosStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplexStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DedekindZetaResidueLeSixteenLogRootDiscrPowStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogUnitarySphereVolumeProductRatioLeLargeRankStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySphereVolumeProductRatioAndInvBoundsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeDedekindZetaRealValueAndLeZetaPowStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

namespace ConstBd

theorem dimN_le (n a : ℕ) (j : Fin a → ℕ) (h : 2 * ∑ i, j i ≤ n) :
    (dimN n j : ℝ) ≤ 2 * ((∑ i, j i : ℕ) : ℝ) * n := by
  have h1 := (GlobalTheory.dim_unipotent_radical_identities a (fun i => (j i : ℤ)) n).2.2
  have h2 : (dimN n j : ℤ) ≤ 2 * ((∑ i, j i : ℕ) : ℤ) * n := by
    refine le_trans (le_of_eq ?_) (h1.trans (le_of_eq ?_))
    · unfold dimN
      push_cast [Nat.cast_sub h, Finset.sum_filter]
      rfl
    · push_cast; rfl
  exact_mod_cast h2

theorem rpow_le (v x : ℝ) (hv : 3 / 4 ≤ v) (hx : 0 ≤ x) : v ^ (-x) ≤ Real.exp (x / 3) := by
  have hv0 : 0 < v := by linarith
  rw [Real.rpow_def_of_pos hv0]
  apply Real.exp_le_exp.2
  have h1 := Real.one_sub_inv_le_log_of_pos hv0
  have h2 : v⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ hv0 (by norm_num)]; linarith
  nlinarith

theorem inv_sph_le (J : ℕ) (s : ℝ) (hJ : (J : ℝ) ≤ s) (hJ1 : 1 ≤ J) :
    (sphV J)⁻¹ ≤ Real.exp (J * (s / 2 * Real.log s)) := by
  refine (GlobalTheory.T.unitarySphereVolumeProduct_ratio_and_inv_bounds.2 J).2.trans ?_
  have h1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have h0 : (0 : ℝ) < J := by linarith
  rw [← Real.exp_log (pow_pos h0 _), Real.log_pow]
  apply Real.exp_le_exp.2
  have h2 : ((J * (J - 1) / 2 : ℕ) : ℝ) ≤ J * (s / 2) := by
    have h3 : ((J * (J - 1) / 2 : ℕ) : ℝ) ≤ ((J * (J - 1) : ℕ) : ℝ) / (2 : ℕ) := Nat.cast_div_le
    rw [Nat.cast_mul, Nat.cast_sub hJ1] at h3
    push_cast at h3
    nlinarith
  have h4 : Real.log J ≤ Real.log s := Real.log_le_log h0 hJ
  have h5 : 0 ≤ Real.log J := Real.log_nonneg h1
  calc _ ≤ (J * (s / 2)) * Real.log s := mul_le_mul h2 h4 h5 (by nlinarith)
    _ = _ := by ring

theorem zeta_prod (E : Type) [Field E] [NumberField E] (J : ℕ) :
    0 ≤ ∏ l ∈ Finset.Icc 2 J, zetaE E l ∧
      ∏ l ∈ Finset.Icc 2 J, zetaE E l ≤ Real.exp (Module.finrank ℚ E) := by
  have h0 : ∀ l ∈ Finset.Icc 2 J, 0 ≤ zetaE E l := fun l hl =>
    zero_le_one.trans (GlobalTheory.T.one_le_dedekindZetaRealValue_and_le_zeta_pow E l (Finset.mem_Icc.1 hl).1).1
  refine ⟨Finset.prod_nonneg h0, ?_⟩
  refine (Finset.prod_le_prod h0 fun l hl => (GlobalTheory.T.one_le_dedekindZetaRealValue_and_le_zeta_pow E l (Finset.mem_Icc.1 hl).1).2).trans ?_
  rw [Finset.prod_pow, ← Real.exp_one_pow]
  apply pow_le_pow_left₀ (Finset.prod_nonneg fun l _ => GlobalTheory.ZetaProd.zeta_nonneg l)
  have := GlobalTheory.zetaProd_sphereVolume_bounds.1 J
  have := Real.exp_one_gt_d9
  linarith

theorem numeric (N s L c : ℝ) (hs : 100 ≤ s) (hN : N = s * s) (hL : 15 ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ 2) :
    N / 3 + (c - (N - 2 * s) * (L - (c + 1)) + 3.49 + s / 2 * (L / 2)) + 2 * (3 + N) + 2 + 1 ≤
      -(1 / 2 * N * L) := by
  have h1 : 100 * s ≤ N := by nlinarith
  have h2 : (N - 2 * s) * (c + 1) ≤ N * 3 := mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have h3 : 100 * s * L ≤ N * L := mul_le_mul_of_nonneg_right h1 (by linarith)
  have h4 : N * 15 ≤ N * L := mul_le_mul_of_nonneg_left hL (by linarith)
  nlinarith

end ConstBd

set_option maxHeartbeats 1000000 in
open ConstBd in

theorem constantBound : ConstantBound := by
  intro E _ _ _ hE p q a j hj1 hjq hL hq hrd _
  obtain ⟨hdeg, hf1, hv, -⟩ := GlobalTheory.T.rootDiscr_ge_three_halves_of_isTotallyComplex E hE.1
  obtain ⟨hres0, hres⟩ := GlobalTheory.T.dedekindZeta_residue_le_sixteen_log_rootDiscr_pow E hE.1
  unfold kapBd
  have haJ : a ≤ ∑ i, j i := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hj1 i)
  have hjJ : ∀ i, j i ≤ ∑ i, j i := fun i =>
    Finset.single_le_sum (f := j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hD := dimN_le (p + q) a j
  have hcast : ((∑ i, j i : ℕ) : ℝ) = ∑ i, (j i : ℝ) := by push_cast; rfl
  generalize hJ : ∑ i, j i = J at *
  have hp : ((p + q : ℕ) : ℝ) = p + q := by push_cast; rfl
  generalize hn : p + q = n at *
  generalize hf : Formalism.HermitianLatticesTheory.fDeg E = f at *
  have hn0 : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num at hL
    · exact_mod_cast h
  have hN : (10000 : ℝ) ≤ n := by
    rw [Real.le_log_iff_exp_le hn0] at hL
    have h1 : Real.exp 15 = Real.exp 1 ^ 15 := by rw [Real.exp_one_pow]; norm_num
    have h2 : (2 : ℝ) ^ 15 ≤ Real.exp 1 ^ 15 :=
      pow_le_pow_left₀ (by norm_num) (by have := Real.exp_one_gt_d9; linarith) _
    norm_num at h2
    linarith
  set s := Real.sqrt n with hs
  have hss : (n : ℝ) = s * s := (Real.mul_self_sqrt hn0.le).symm
  have hs100 : 100 ≤ s := Real.le_sqrt_of_sq_le (by linarith)
  have hqs : (q : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by exact_mod_cast hq)
  have hJq : (J : ℝ) ≤ q := by exact_mod_cast hjq
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have haJ' : (a : ℝ) ≤ J := by exact_mod_cast haJ
  have h100 : 100 * s ≤ n := by nlinarith
  have h2J : 2 * J + 2 ≤ n := by
    have : (2 : ℝ) * J + 2 ≤ n := by linarith
    exact_mod_cast this
  have hJp : J ≤ p := by
    have : (J : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hlogs : Real.log s = Real.log n / 2 := Real.log_sqrt hn0.le
  have hpos : ∀ i, 0 < sphV i := fun i => (GlobalTheory.T.unitarySphereVolumeProduct_ratio_and_inv_bounds.2 i).1
  have hpi := Real.pi_pos
  have hc0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by have := Real.pi_gt_three; linarith)
  have hc2 : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [Real.exp_one_pow]; norm_num
    have := Real.exp_one_gt_d9
    have := Real.pi_lt_d2
    nlinarith

  have T1 : Formalism.HermitianLatticesTheory.vInv E ^ (-((f : ℝ) * dimN n j / 2)) ≤ Real.exp (f * J * (n / 3)) := by
    refine (rpow_le _ _ (by linarith) (by positivity)).trans (Real.exp_le_exp.2 ?_)
    have := mul_le_mul_of_nonneg_left (hD (by omega)) hf0
    linarith

  have T2 : (2 : ℝ) ^ (-((f : ℝ) * ((n : ℝ) * J - (J : ℝ) ^ 2 + (J : ℝ) / 2))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (0 : ℝ) ≤ (n : ℝ) * J - (J : ℝ) ^ 2 + (J : ℝ) / 2 := by nlinarith
    have := mul_nonneg hf0 this
    linarith

  have hA := GlobalTheory.T.log_unitarySphereVolumeProduct_ratio_le_large_rank n p J (by exact_mod_cast (by linarith : (18 : ℝ) ≤ n)) hJp (by omega)
    (by linarith) (by linarith)
  rw [Real.log_div hn0.ne' (by positivity), Real.log_mul (x := 2 * Real.pi) (by positivity) (by positivity),
    Real.log_exp,
    Real.log_le_iff_le_exp (div_pos (hpos _) (hpos _))] at hA
  have hB := GlobalTheory.T.unitarySphereVolumeProduct_ratio_and_inv_bounds.1 q J hjq
  rw [Real.log_le_iff_le_exp (div_pos (hpos _) (hpos _))] at hB
  have hC : (∏ i, sphV (j i))⁻¹ ≤ Real.exp (J * (s / 2 * (Real.log n / 2))) := by
    rw [← Finset.prod_inv_distrib, hcast, Finset.sum_mul, Real.exp_sum, ← hlogs]
    apply Finset.prod_le_prod (fun i _ => (inv_pos.2 (hpos _)).le)
    intro i _
    apply inv_sph_le _ _ _ (hj1 i)
    have : (j i : ℝ) ≤ J := by exact_mod_cast hjJ i
    linarith
  have hP : 0 < ∏ i, sphV (j i) := Finset.prod_pos fun i _ => hpos _
  have T3 : (sphV p * sphV q / (sphV (p - J) * sphV (q - J) * ∏ i, sphV (j i))) ^ f ≤
      Real.exp (f * J * (Real.log (2 * Real.pi) - (n - 2 * s) * (Real.log n - (Real.log (2 * Real.pi) + 1)) +
        3.49 + s / 2 * (Real.log n / 2))) := by
    rw [mul_assoc (f : ℝ), Real.exp_nat_mul]
    have := hpos p; have := hpos q; have := hpos (p - J); have := hpos (q - J)
    apply pow_le_pow_left₀ (by positivity)
    have e : sphV p * sphV q / (sphV (p - J) * sphV (q - J) * ∏ i, sphV (j i)) =
        sphV p / sphV (p - J) * (sphV q / sphV (q - J)) * (∏ i, sphV (j i))⁻¹ := by
      field_simp
    rw [e]
    refine (mul_le_mul (mul_le_mul hA hB (by positivity) (by positivity)) hC (by positivity)
      (by positivity)).trans (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

  have T4 : dedekindZeta_residue E ^ a ≤ Real.exp (f * J * (2 * (3 + n))) := by
    have h16 : (16 : ℝ) ≤ Real.exp 3 := by
      have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [Real.exp_one_pow]; norm_num
      have h2 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
        pow_le_pow_left₀ (by norm_num) (by have := Real.exp_one_gt_d9; linarith) _
      norm_num at h2
      linarith
    have hl0 : 0 ≤ Real.log (2 * Formalism.HermitianLatticesTheory.vInv E) := Real.log_nonneg (by linarith)
    have h3 : 16 * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ Real.exp (3 + n) := by
      rw [Real.exp_add]
      exact mul_le_mul h16 hrd hl0 (by positivity)
    have h4 := hres.trans (pow_le_pow_left₀ (by positivity) h3 _)
    refine (pow_le_pow_left₀ hres0.le h4 a).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    push_cast
    have : (a : ℝ) * (2 * f * (3 + n)) ≤ J * (2 * f * (3 + n)) :=
      mul_le_mul_of_nonneg_right haJ' (by positivity)
    linarith

  have T5 : ∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l ≤ Real.exp (f * J * 2) := by
    refine (Finset.prod_le_prod (fun i _ => (zeta_prod E (j i)).1)
      (fun i _ => (zeta_prod E (j i)).2)).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul, hdeg]
    apply Real.exp_le_exp.2
    push_cast
    have := mul_le_mul_of_nonneg_right haJ' hf0
    linarith
  have T5' : 0 ≤ ∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l :=
    Finset.prod_nonneg fun i _ => (zeta_prod E (j i)).1

  obtain ⟨hL1, hL0⟩ := GlobalTheory.T.neg_log_prod_lValEta_le_and_pos E hE (n - 2 * J) n (by omega)
  rw [hf] at hL1
  have FreeQuotientRank : (∏ M ∈ Finset.Ioc (n - 2 * J) n, Formalism.HermitianLatticesTheory.lValEta E M)⁻¹ ≤ Real.exp (f * J * 1) := by
    rcases Nat.eq_zero_or_pos J with h | h
    · subst h; simp
    · rw [← Real.log_le_iff_le_exp (inv_pos.2 hL0), Real.log_inv]
      refine hL1.trans ?_
      have h1 : (2 : ℝ) ^ ((1 : ℤ) - (n - 2 * J : ℕ)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
      have h2 : (1 : ℝ) ≤ J := by exact_mod_cast h
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left (h1.trans h2) hf0
  have hv0 : 0 < Formalism.HermitianLatticesTheory.vInv E := by linarith
  have := hpos p; have := hpos q; have := hpos (p - J); have := hpos (q - J)
  rw [div_eq_mul_inv]
  refine (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul T1 T2 (by positivity) (by positivity))
    T3 (by positivity) (by positivity)) T4 (by positivity) (by positivity)) T5 T5' (by positivity)) FreeQuotientRank
    (by positivity) (by positivity)).trans ?_
  rw [mul_one, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_left (numeric n s _ _ hs100 hss hL hc0 hc2) (mul_nonneg hf0 hJ0)
  linarith

end GlobalTheory.FlagMeas
