import Formalism.HermitianCurvature.LowerBlockNormalisedBoundFromComponents

open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.FrameIntegralJacobian

open Formalism.FourierDecayAlt.PairingProductCorollary

theorem factorsPositive_ok : FactorsPositive := by
  unfold FactorsPositive
  refine ⟨fun D h0 h1 => ?_, fun d h1 h2 => ?_, fun D h0 h1 => div_neg_of_pos_of_neg h0 (by linarith)⟩
  · simp only [div_pos_iff, lt_abs]
    constructor
    · rintro ⟨⟨ha, hb⟩ | ⟨ha, hb⟩, ⟨hc, hd⟩ | ⟨hc, hd⟩⟩ <;>
        first | (left; linarith) | (right; linarith) | (exfalso; linarith)
    · rintro (h | h)
      · exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩
      · exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩
  · simp only [div_pos_iff]
    constructor
    · rintro ⟨⟨ha, hb⟩ | ⟨ha, hb⟩, ⟨hc, hd⟩ | ⟨hc, hd⟩⟩ <;>
        first | (left; linarith) | (right; linarith) | (exfalso; linarith)
    · rintro (h | h)
      · exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩
      · exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩

theorem cutRoom_ok : CutRoom := by
  unfold CutRoom
  intro r α β h
  refine ⟨by ring, fun k hk => ⟨?_, ?_⟩⟩
  · have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  · have hk' : ((k:ℝ) + 1) ≤ 6 * ((r:ℝ) + 1) ^ 2 := by
      exact_mod_cast (show k + 1 ≤ 6 * (r + 1) ^ 2 from hk)
    linarith

private lemma bern_lemma (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hx : 0 ≤ 1 - x := by linarith
    have hm := mul_le_mul_of_nonneg_right ih hx
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (mul_nonneg h0 h0)]

theorem weightLower_ok : WeightLower := by
  unfold WeightLower
  intro N m f hN hm hf
  have hN4 : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N:ℝ) ≠ 0 := by positivity
  have hxN2 : 1 / (N:ℝ) ^ 2 * (N:ℝ) ^ 2 = 1 := by field_simp
  have hx0 : 0 ≤ 1 / (N:ℝ) ^ 2 := by positivity
  have hNx : (N:ℝ) * (1 / (N:ℝ) ^ 2) ≤ 1 / 4 := by
    nlinarith [mul_nonneg (mul_nonneg hx0 (by linarith : (0:ℝ) ≤ N)) (by linarith : (0:ℝ) ≤ (N:ℝ) - 4)]
  have hx1 : 1 / (N:ℝ) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx0 (by linarith : (0:ℝ) ≤ (N:ℝ) - 4)]
  have ht0 : 0 ≤ 1 - 1 / (N:ℝ) ^ 2 := by linarith
  have ht1 : 1 - 1 / (N:ℝ) ^ 2 ≤ 1 := by linarith
  have hprod : ∏ _i : Fin m, (1 - 1 / (N:ℝ) ^ 2) ≤ ∏ i, f i :=
    Finset.prod_le_prod (fun i _ => ht0) (fun i _ => hf i)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hpow : (1 - 1 / (N:ℝ) ^ 2) ^ N ≤ (1 - 1 / (N:ℝ) ^ 2) ^ m :=
    pow_le_pow_of_le_one ht0 ht1 hm
  have hbern := bern_lemma (1 / (N:ℝ) ^ 2) hx0 hx1 N
  have hexp : Real.exp (-(1 / 2)) ≤ 3 / 4 := by
    have e1 := Real.add_one_le_exp (1 / 2 : ℝ)
    have e2 : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have e3 := Real.exp_pos (-(1 / 2))
    nlinarith
  linarith

theorem blockPhase_ok : BlockPhase := by
  unfold BlockPhase
  intro s x
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h1 : Complex.I ^ ((s:ℤ) - 1 - 2 * x) = Complex.I ^ ((s:ℤ) - 1) * ((Complex.I ^ 2) ^ x)⁻¹ := by
    rw [sub_eq_add_neg ((s:ℤ) - 1), zpow_add₀ hI, zpow_neg, ← pow_mul]
    norm_cast
  rw [h1, Complex.I_sq, mul_assoc, inv_mul_cancel₀ (pow_ne_zero x (by norm_num : (-1:ℂ) ≠ 0)), mul_one]

theorem stdFramePhase_ok : StdFramePhase := by
  unfold StdFramePhase
  intro ka a b ha hb
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hab : a' + 1 + (b' + 1) - 2 = b' + a' := by omega
  have hconj : starRingEnd ℂ (Complex.I * ka) = Complex.I⁻¹ * ka := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.inv_I]
  have hz : Complex.I ^ (((b' + 1 : ℕ) : ℤ) - ((a' + 1 : ℕ) : ℤ)) = Complex.I ^ b' / Complex.I ^ a' := by
    rw [show (((b' + 1 : ℕ) : ℤ) - ((a' + 1 : ℕ) : ℤ)) = (b' : ℤ) - (a' : ℤ) by push_cast; ring,
      zpow_sub₀ Complex.I_ne_zero, zpow_natCast, zpow_natCast]
  simp only [Nat.add_sub_cancel]
  rw [hab, hconj, mul_pow, mul_pow, inv_pow, pow_add, hz]
  ring

theorem realFrameEntry_ok : RealFrameEntry := by
  unfold RealFrameEntry
  intro rd r a b i s hrd
  refine ⟨?_, fun h => by omega⟩
  rw [← zpow_add₀ hrd.ne']
  congr 1
  ring

theorem gaExponent_ok : GaExponent := by
  unfold GaExponent
  refine ⟨fun ka l M hM => ?_, fun r k hk => ?_⟩
  · rw [← pow_mul]
    congr 1
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl
      simp
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have h1 : 2 * (l' + 1) - 2 = 2 * l' := by omega
      have h2 : 2 * (M' + 2 - 2) + 2 = 2 * (M' + 1) := by omega
      have h3 : l' + 1 - 1 = l' := by omega
      have h4 : M' + 2 - 1 = M' + 1 := by omega
      rw [h1, h2, h3, h4]
      ring
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h1 : k' + 1 - 1 = k' := by omega
    have h2 : k' + 1 + 1 - 1 = k' + 1 := by omega
    rw [h1, h2]
    ring

theorem realCharacter_ok : RealCharacter := by
  unfold RealCharacter
  intro g rd x hg hrd
  have hg' : (g:ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hrd' : (rd:ℂ) ≠ 0 := by exact_mod_cast hrd.ne'
  congr 1
  rw [map_mul, Complex.conj_ofReal]
  push_cast
  field_simp
  try ring

theorem placesCombine_ok : PlacesCombine := by
  unfold PlacesCombine
  intro ι _ _ K abelian₂ o N S hL hS h
  have hpos : 0 < ∏ v ∈ univ.filter (fun v => abelian₂ v < o v), o v ^ K := by
    apply Finset.prod_pos
    intro v hv
    have hv' : abelian₂ v < o v := (Finset.mem_filter.mp hv).2
    exact pow_pos (lt_of_le_of_lt (hL v) hv') K
  have hprod : ∏ v, minFac (abelian₂ v) (o v) K =
      (∏ v ∈ univ.filter (fun v => abelian₂ v < o v), abelian₂ v ^ K) /
        (∏ v ∈ univ.filter (fun v => abelian₂ v < o v), o v ^ K) := by
    simp only [minFac, div_pow]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_div_distrib]
  rw [hprod, div_mul_eq_mul_div, le_div_iff₀ hpos, mul_comm N]
  exact h

theorem corAConstWave_ok : CorAConstWave := by
  unfold CorAConstWave
  refine ⟨fun n ell Qw BBs BB hell hn hQ0 hQ hB0 hB => ?_, fun Qw BBs BB hQ0 hQ hB0 hB => ?_⟩
  · have h2 : Real.exp (1 / 2) = Real.exp (1 / 4) ^ 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    have hs : Real.sqrt Qw ≤ Real.exp (1 / 4) := by
      calc Real.sqrt Qw ≤ Real.sqrt (Real.exp (1 / 4) ^ 2) := Real.sqrt_le_sqrt (by rw [← h2]; exact hQ)
        _ = Real.exp (1 / 4) := Real.sqrt_sq (Real.exp_pos _).le
    have h4 : 0 ≤ 4 / ell := div_nonneg (by norm_num) hell.le
    have hP : 0 ≤ (1 / 2 : ℝ) * (4 / ell) ^ n := mul_nonneg (by norm_num) (pow_nonneg h4 n)
    have hm : Real.sqrt Qw * BBs ≤ Real.exp (1 / 4) * BB :=
      mul_le_mul hs hB hB0 (Real.exp_pos _).le
    calc (1 / 2) * (4 / ell) ^ n * Real.sqrt Qw * BBs
        = ((1 / 2) * (4 / ell) ^ n) * (Real.sqrt Qw * BBs) := by ring
      _ ≤ ((1 / 2) * (4 / ell) ^ n) * (Real.exp (1 / 4) * BB) := mul_le_mul_of_nonneg_left hm hP
      _ = Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ n * BB := by ring
  · have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    have hs : Real.sqrt Qw ≤ Real.exp 1 := by
      calc Real.sqrt Qw ≤ Real.sqrt (Real.exp 1 ^ 2) := Real.sqrt_le_sqrt (by rw [← h2]; exact hQ)
        _ = Real.exp 1 := Real.sqrt_sq (Real.exp_pos _).le
    exact mul_le_mul hs hB hB0 (Real.exp_pos _).le

theorem weightedKernelPSD_ok : WeightedKernelPSD := by
  unfold WeightedKernelPSD
  intro H _ Kn n hK hn
  classical
  have hst : ∀ h : H, star (((Real.sqrt (n h) : ℝ)) : ℂ) = ((Real.sqrt (n h) : ℝ) : ℂ) :=
    fun h => Complex.conj_ofReal _
  have hB := hK.conjTranspose_mul_mul_same (Matrix.diagonal fun h => ((Real.sqrt (n h) : ℝ) : ℂ))
  convert hB using 1
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Pi.star_apply,
    hst, Matrix.of_apply, Complex.ofReal_mul]
  try ring

theorem scaleBeta_ok : ScaleBeta := by
  unfold ScaleBeta
  intro ka Pp q r hka hq hP
  have hk0 : ka ≠ 0 := hka.ne'
  have e1 : Pp / (ka ^ (4 * r) * q) = Pp / q / (ka ^ (2 * r)) ^ 2 := by
    rw [← pow_mul, div_div, mul_comm q, show 2 * r * 2 = 4 * r by ring]
  have e2 : ka ^ (-(1 + 2 * r : ℤ)) = (ka * ka ^ (2 * r))⁻¹ := by
    rw [zpow_neg, ← pow_succ', show (1 + 2 * (r:ℤ)) = ((2 * r + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
  rw [e1, Real.sqrt_div (div_nonneg hP hq.le), Real.sqrt_sq (pow_nonneg hka.le (2 * r)), e2, mul_inv,
    ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hk0, one_mul, div_eq_inv_mul]

theorem frameIntegral_ok : FrameIntegral := by
  unfold FrameIntegral
  intro ka de Cst ph pht Rt R hka hde hph hRt hR
  have hk0 : ka ≠ 0 := hka.ne'
  have hcv : ∫ x : ℂ, pht (ka • x) = |(ka ^ 2)⁻¹| • ∫ x : ℂ, pht x := by
    have h := MeasureTheory.Measure.integral_comp_smul
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ)) pht ka
    rw [Complex.finrank_real_complex] at h
    exact h
  have hfun : ∀ c : ℂ, ph c * (de : ℂ) = (Cst * ka ^ 2 : ℝ) • pht (ka • c) := by
    intro c
    rw [hph c, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  simp_rw [hfun]
  rw [MeasureTheory.integral_smul, hcv, smul_smul, hRt, hR, abs_of_pos (inv_pos.mpr (pow_pos hka 2)),
    Complex.real_smul, mul_assoc Cst, mul_inv_cancel₀ (pow_ne_zero 2 hk0), mul_one]

theorem frameJacobian_ok : FrameJacobian := by
  unfold FrameJacobian
  intro ka m g hka
  have hk0 : ka ≠ 0 := hka.ne'
  have hk0c : (ka : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hcv : ∫ x : ℂ, ((‖ka • x‖ ^ (2 * m) : ℝ) : ℂ) * g (ka • x)
      = |(ka ^ 2)⁻¹| • ∫ x : ℂ, ((‖x‖ ^ (2 * m) : ℝ) : ℂ) * g x := by
    have h := MeasureTheory.Measure.integral_comp_smul
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
      (fun z : ℂ => ((‖z‖ ^ (2 * m) : ℝ) : ℂ) * g z) ka
    rw [Complex.finrank_real_complex] at h
    exact h
  have hpt : ∀ c : ℂ, ((‖c‖ ^ (2 * m) : ℝ) : ℂ) * g ((ka : ℂ) * c)
      = ((ka ^ (2 * m))⁻¹ : ℝ) • (((‖ka • c‖ ^ (2 * m) : ℝ) : ℂ) * g (ka • c)) := by
    intro c
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hka, mul_pow, Complex.real_smul, Complex.real_smul]
    push_cast
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hk0c), one_mul]
  have hreal : ka ^ (2 * m + 2) * ((ka ^ (2 * m))⁻¹ * (ka ^ 2)⁻¹) = 1 := by
    rw [pow_add, mul_mul_mul_comm, mul_inv_cancel₀ (pow_ne_zero _ hk0),
      mul_inv_cancel₀ (pow_ne_zero _ hk0), one_mul]
  simp_rw [hpt]
  rw [MeasureTheory.integral_smul, hcv, smul_smul, abs_of_pos (inv_pos.mpr (pow_pos hka 2)), Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul, hreal, Complex.ofReal_one, one_mul]

end Formalism.FourierDecayAlt.P.FrameIntegralJacobian

theorem Formalism.FourierDecayAlt.P.local_factors_positive : Formalism.FourierDecayAlt.PairingProductCorollary.FactorsPositive := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.factorsPositive_ok
theorem Formalism.FourierDecayAlt.P.truncation_room_estimate : Formalism.FourierDecayAlt.PairingProductCorollary.CutRoom := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.cutRoom_ok
theorem Formalism.FourierDecayAlt.P.weight_lower_bound : Formalism.FourierDecayAlt.PairingProductCorollary.WeightLower := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.weightLower_ok
theorem Formalism.FourierDecayAlt.P.block_phase_identity : Formalism.FourierDecayAlt.PairingProductCorollary.BlockPhase := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.blockPhase_ok
theorem Formalism.FourierDecayAlt.P.standard_frame_phase_alt : Formalism.FourierDecayAlt.PairingProductCorollary.StdFramePhase := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.stdFramePhase_ok
theorem Formalism.FourierDecayAlt.P.real_frame_entry_alt : Formalism.FourierDecayAlt.PairingProductCorollary.RealFrameEntry := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.realFrameEntry_ok
theorem Formalism.FourierDecayAlt.P.gamma_exponent_formula : Formalism.FourierDecayAlt.PairingProductCorollary.GaExponent := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.gaExponent_ok
theorem Formalism.FourierDecayAlt.P.real_character_identity : Formalism.FourierDecayAlt.PairingProductCorollary.RealCharacter := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.realCharacter_ok
theorem Formalism.FourierDecayAlt.P.local_places_combine : Formalism.FourierDecayAlt.PairingProductCorollary.PlacesCombine := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.placesCombine_ok
theorem Formalism.FourierDecayAlt.P.constant_wave_corollary : Formalism.FourierDecayAlt.PairingProductCorollary.CorAConstWave := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.corAConstWave_ok
theorem Formalism.FourierDecayAlt.P.weighted_kernel_posSemidef : Formalism.FourierDecayAlt.PairingProductCorollary.WeightedKernelPSD := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.weightedKernelPSD_ok
theorem Formalism.FourierDecayAlt.P.scaling_beta_identity : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleBeta := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.scaleBeta_ok
theorem Formalism.FourierDecayAlt.P.frame_integral_formula_alt : Formalism.FourierDecayAlt.PairingProductCorollary.FrameIntegral := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.frameIntegral_ok
theorem Formalism.FourierDecayAlt.P.frame_jacobian_formula : Formalism.FourierDecayAlt.PairingProductCorollary.FrameJacobian := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.frameJacobian_ok

end
