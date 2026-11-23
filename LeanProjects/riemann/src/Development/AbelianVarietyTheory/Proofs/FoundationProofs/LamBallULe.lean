import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc

noncomputable section
namespace GlobalTheory.CartanInt.LamBall
open Formalism.BasicNotions Matrix MeasureTheory

theorem pow_self_le_factorial_sq (n : ℕ) : n ^ n ≤ n.factorial ^ 2 := by
  have h1 : ∏ k ∈ Finset.range n, (k + 1) = n.factorial := Finset.prod_range_add_one_eq_factorial n
  have h2 : ∏ k ∈ Finset.range n, (n - k) = n.factorial := by
    calc ∏ k ∈ Finset.range n, (n - k) = ∏ k ∈ Finset.range n, ((n - 1 - k) + 1) :=
          Finset.prod_congr rfl fun k hk => by have := Finset.mem_range.1 hk; omega
      _ = ∏ k ∈ Finset.range n, (k + 1) := Finset.prod_range_reflect (fun k => k + 1) n
      _ = n.factorial := h1
  calc n ^ n = ∏ _k ∈ Finset.range n, n := by rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ k ∈ Finset.range n, ((k + 1) * (n - k)) := by
        apply Finset.prod_le_prod'
        intro k hk
        have hk := Finset.mem_range.1 hk
        obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
        have hn : n = k + m + 1 := by omega
        rw [hm, hn]
        nlinarith
    _ = n.factorial ^ 2 := by rw [Finset.prod_mul_distrib, h1, h2, sq]

theorem two_mul_pow_le_factorial (N : ℕ) : (2 * N) ^ N ≤ (2 * N).factorial := by
  have h := pow_self_le_factorial_sq (2 * N)
  rw [pow_mul'] at h
  exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h

theorem volume_l1_ball_le {ι : Type} [Fintype ι] (a : ℕ) (ha : Fintype.card ι = a ^ 2) (r : ℝ)
    (hr : 0 < r) : (volume : Measure (ι → ℂ)) {z | ∑ i, ‖z i‖ < 2 * r} ≤
      ENNReal.ofReal ((18 / 5 * r / (a : ℝ)) ^ (a ^ 2)) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (by simpa using ha)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero,
      ENNReal.ofReal_one, one_pow]
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    exact prob_le_one
  · have hnpos : (0 : ℝ) < Fintype.card ι := by rw [ha]; push_cast; positivity
    have : Nonempty ι := Fintype.card_pos_iff.1 (by rw [ha]; positivity)
    have hset : {z : ι → ℂ | ∑ i, ‖z i‖ < 2 * r} =
        {z | (∑ i, ‖z i‖ ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) < 2 * r} := by
      simp only [Real.rpow_one, div_one]
    have hG3 : Real.Gamma (2 / 1 + 1) = 2 := by
      have := Real.Gamma_nat_eq_factorial 2
      norm_num at this ⊢
    have hGn : Real.Gamma (2 * (Fintype.card ι : ℝ) / 1 + 1) = ((2 * Fintype.card ι).factorial : ℝ) := by
      rw [div_one, ← Real.Gamma_nat_eq_factorial]
      push_cast
      ring_nf
    rw [hset, Complex.volume_sum_rpow_lt ι le_rfl, hG3, hGn, ← ha,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_pow (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set n := Fintype.card ι with hn
    have hfac : ((2 : ℝ) * n) ^ n ≤ ((2 * n).factorial : ℝ) := by
      exact_mod_cast two_mul_pow_le_factorial n
    have han : (a : ℝ) ^ 2 = n := by exact_mod_cast ha.symm
    calc (2 * r) ^ (2 * n) * ((Real.pi * 2) ^ n / ((2 * n).factorial : ℝ))
        = (8 * Real.pi * r ^ 2) ^ n / ((2 * n).factorial : ℝ) := by
          rw [pow_mul, ← mul_div_assoc, ← mul_pow]
          congr 2
          ring
      _ ≤ (8 * Real.pi * r ^ 2) ^ n / ((2 : ℝ) * n) ^ n :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity) n) hfac
      _ = (4 * Real.pi * r ^ 2 / n) ^ n := by
          rw [← div_pow]
          congr 1
          field_simp
          ring
      _ ≤ (324 / 25 * r ^ 2 / n) ^ n := by
          apply pow_le_pow_left₀ (by positivity)
          gcongr
          linarith [Real.pi_lt_d2]
      _ = ((18 / 5 * r / a) ^ 2) ^ n := by
          congr 1
          rw [div_pow, han]
          ring
      _ = ((18 / 5 * r / a) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem lam_ballU_le (p q : ℕ) (lam : Measure (lieU p q)) (h : IsOmegaLeb lam) (r : ℝ) (hr : 0 < r) :
    lam (ballU p q r) ≤ ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) := by
  classical
  obtain ⟨hHaar, hmap⟩ := h
  have : BorelSpace (lieU p q) := ⟨rfl⟩
  have hcont : Continuous fun X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ =>
      Xᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add
      (continuous_const.matrix_mul continuous_id)
  have hcl : IsClosed (lieU p q : Set (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :=
    isClosed_eq hcont continuous_const
  have : LocallyCompactSpace (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ))
  have : SecondCountableTopology (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ))
  have : LocallyCompactSpace (lieU p q) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (lieU p q) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have : OpensMeasurableSpace (lieU p q × lieU p q) := inferInstance
  have : IsLocallyFiniteMeasure lam := inferInstance
  have : SigmaFinite lam := inferInstance
  have hc : Continuous fun ab : lieU p q × lieU p q =>
      (ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    have h1 : Continuous fun ab : lieU p q × lieU p q =>
        (ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous fun ab : lieU p q × lieU p q =>
        (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := continuous_subtype_val.comp continuous_snd
    h1.add (h2.const_smul Complex.I)
  have hΦ : Measurable fun ab : lieU p q × lieU p q =>
      entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :=
    (continuous_pi fun ij : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) => hc.matrix_elem ij.1 ij.2).measurable
  have hS : MeasurableSet {z : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) → ℂ | ∑ i, ‖z i‖ < 2 * r} :=
    (isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).norm)
      continuous_const).measurableSet
  have hsub : ballU p q r ×ˢ ballU p q r ⊆ (fun ab : lieU p q × lieU p q =>
      entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))) ⁻¹'
      {z | ∑ i, ‖z i‖ < 2 * r} := by
    rintro ⟨X, Y⟩ ⟨hX, hY⟩
    simp only [ballU, Set.mem_ofPred_eq] at hX hY
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, entries, Fintype.sum_prod_type]
    calc ∑ i, ∑ j, ‖((X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
          Complex.I • (Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) i j‖
        ≤ ∑ i, ∑ j, (‖(X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ +
          ‖(Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          calc _ ≤ _ := norm_add_le _ _
            _ = _ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ = (∑ i, ∑ j, ‖(X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) +
          ∑ i, ∑ j, ‖(Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
          simp only [Finset.sum_add_distrib]
      _ < r + r := add_lt_add hX hY
      _ = 2 * r := by ring
  have hvol := volume_l1_ball_le (ι := (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q)) (p + q)
    (by simp [Fintype.card_prod, Fintype.card_sum, sq]) r hr
  have key : lam (ballU p q r) ^ 2 ≤
      ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) ^ 2 := by
    calc lam (ballU p q r) ^ 2 = (lam.prod lam) (ballU p q r ×ˢ ballU p q r) := by
          rw [Measure.prod_prod, sq]
      _ ≤ (lam.prod lam) ((fun ab : lieU p q × lieU p q =>
            entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
              Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))) ⁻¹'
            {z | ∑ i, ‖z i‖ < 2 * r}) := measure_mono hsub
      _ = ((lam.prod lam).map (fun ab : lieU p q × lieU p q =>
            entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
              Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))))
            {z | ∑ i, ‖z i‖ < 2 * r} := (Measure.map_apply hΦ hS).symm
      _ = volume {z : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) → ℂ | ∑ i, ‖z i‖ < 2 * r} := by
          rw [hmap]
      _ ≤ _ := hvol
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 key

end GlobalTheory.CartanInt.LamBall
