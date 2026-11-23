import Formalism.FlagUnipotentLattices.UnitSumBound

open Finset Formalism.HermitianLatticeCounting.LocalIntegralStructure

namespace Formalism.HermitianLatticeCounting.P

lemma volU_pos_minkowski_factorial_bounds (j : ℕ) : 0 < volU j := by
  unfold volU; apply prod_pos; intro i _; positivity

lemma volU_succ' (j : ℕ) : volU (j + 1) = volU j * ((2 * Real.pi) ^ (j + 1) / (j.factorial : ℝ)) := by
  unfold volU
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem volume_ratio_increment : Formalism.HermitianLatticeCounting.LocalIntegralStructure.VolStep := by
  intro j
  rw [volU_succ']
  have := volU_pos_minkowski_factorial_bounds j
  field_simp

theorem volume_ratio_formula : Formalism.HermitianLatticeCounting.LocalIntegralStructure.VolRatio := by
  intro k p
  induction p with
  | zero => simp [(volU_pos_minkowski_factorial_bounds k).ne']
  | succ p ih =>
    rw [← add_assoc, volU_succ', Finset.prod_Ico_succ_top (by omega)]
    have e : (p + 1) * k + (p + 1) * (p + 1 + 1) / 2 = (p * k + p * (p + 1) / 2) + (k + p + 1) := by
      have h1 : (p + 1) * (p + 1 + 1) = p * (p + 1) + 2 * (p + 1) := by ring
      rw [h1, Nat.add_mul_div_left _ _ (by norm_num)]; ring
    rw [e, pow_add _ (p * k + p * (p + 1) / 2), ← ih]
    have := volU_pos_minkowski_factorial_bounds k
    have h3 : ((k + p).factorial : ℝ) ≠ 0 := by positivity
    field_simp

theorem constant_product_formula : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ConstProduct := by
  intro j r T T' g v n0 κ dimpi Vd VV hT hT' hg hv hVV hn
  have hR := volume_ratio_formula (j + 1) (2 * r + 1)
  have hS := volume_ratio_increment j
  have p0 := volU_pos_minkowski_factorial_bounds j
  have p1 := volU_pos_minkowski_factorial_bounds (j + 1)
  have p2 := volU_pos_minkowski_factorial_bounds (j + 1 + (2 * r + 1))
  have hsplit : ∏ i ∈ range (j + 1 + (2 * r + 1)), (i.factorial : ℝ) =
      (∏ i ∈ range (j + 1), (i.factorial : ℝ)) * ∏ i ∈ Ico (j + 1) (j + 1 + (2 * r + 1)), (i.factorial : ℝ) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.prod_Ico_consecutive _ (by omega) (by omega)]
  set F1 := ∏ i ∈ range (j + 1), (i.factorial : ℝ) with hF1
  set F2 := ∏ i ∈ Ico (j + 1) (j + 1 + (2 * r + 1)), (i.factorial : ℝ) with hF2
  have hF1p : 0 < F1 := prod_pos (fun i _ => by positivity)
  have hF2p : 0 < F2 := prod_pos (fun i _ => by positivity)
  rw [hsplit]
  have hpi := Real.pi_pos

  have L : n0 * (T * T') ^ j *
      (dimpi * (Vd / F1) * volU (j + 1 + (2 * r + 1)) * volU j /
        (VV / (F1 * F2) * volU (j + 1) ^ 2 * (2 * v) ^ (2 * r * (j + 1)))) =
      (n0 * (volU j / volU (j + 1))) * (volU (j + 1 + (2 * r + 1)) / volU (j + 1) * F2) * (T * T') ^ j *
        dimpi * (Vd / VV) / (2 * v) ^ (2 * r * (j + 1)) := by
    field_simp
  have hn' : n0 * ((j.factorial : ℝ) / (2 * Real.pi) ^ (j + 1)) =
      κ / (g ^ (2 * r + 2) * T * (2 * v)) ^ (j + 1) := by rw [← hn, mul_div_assoc]
  rw [L, hR, hS, hn']
  have e2 : (T * T') ^ j = (T * T') ^ (j + 1) / (T * T') := by rw [pow_succ]; field_simp
  have e3 : (2 * Real.pi) ^ ((2 * r + 1) * (j + 1)) = ((2 * Real.pi) ^ (2 * r + 1)) ^ (j + 1) := by rw [pow_mul]
  have e4 : (2 * v) ^ (2 * r * (j + 1)) = ((2 * v) ^ (2 * r)) ^ (j + 1) := by rw [pow_mul]
  have e5 : (T' / g ^ (2 * r + 2) * (Real.pi / v) ^ (2 * r + 1)) =
      (T * T') * (2 * Real.pi) ^ (2 * r + 1) / ((g ^ (2 * r + 2) * T * (2 * v)) * (2 * v) ^ (2 * r)) := by
    rw [div_pow, mul_pow 2 Real.pi, mul_pow 2 v (2 * r)]
    field_simp
    ring
  rw [pow_add (2 * Real.pi) ((2 * r + 1) * (j + 1)), e2, e3, e4, e5, div_pow, mul_pow (T * T'),
    mul_pow (g ^ (2 * r + 2) * T * (2 * v))]
  have hX : (g ^ (2 * r + 2) * T * (2 * v)) ^ (j + 1) ≠ 0 := by positivity
  have hZ : ((2 * v) ^ (2 * r)) ^ (j + 1) ≠ 0 := by positivity
  generalize (g ^ (2 * r + 2) * T * (2 * v)) ^ (j + 1) = X at hX ⊢
  generalize ((2 * v) ^ (2 * r)) ^ (j + 1) = Z0 at hZ ⊢
  generalize ((2 * Real.pi) ^ (2 * r + 1)) ^ (j + 1) = Y
  generalize (T * T') ^ (j + 1) = Q
  generalize (2 * Real.pi) ^ ((2 * r + 1) * (2 * r + 1 + 1) / 2) = S
  field_simp

theorem critical_threshold_form : Formalism.HermitianLatticeCounting.LocalIntegralStructure.TcritForm := by
  intro k r T' g v rd Vd VV Tc hT' hg hv hrd hVd hVV hTc h
  have hpi := Real.pi_pos
  have hρ : 0 < rd ^ (((2 * r + 1 : ℕ) : ℝ) / 2) := Real.rpow_pos_of_pos hrd _
  generalize rd ^ (((2 * r + 1 : ℕ) : ℝ) / 2) = ρ at h hρ ⊢
  have hka : 0 < Real.pi / v := by positivity
  generalize Real.pi / v = ka at h hka ⊢
  generalize (2 * r + 2) * (2 * r + 1) / 2 = N at h ⊢
  rw [pow_add, pow_add, pow_mul, mul_comm k, pow_mul] at h
  rw [mul_pow, div_pow, inv_pow, div_pow, div_pow]
  have h1 : 0 < (g ^ (2 * r + 2)) ^ k := by positivity
  have h2 : 0 < (ka ^ (2 * r + 1)) ^ k := by positivity
  have h3 : 0 < Tc ^ k := by positivity
  have h4 : 0 < T' ^ k := by positivity
  have h5 : 0 < g ^ N := by positivity
  have h6 : 0 < ka ^ N := by positivity
  generalize (g ^ (2 * r + 2)) ^ k = A at h h1 ⊢
  generalize (ka ^ (2 * r + 1)) ^ k = B at h h2 ⊢
  generalize Tc ^ k = C at h h3 ⊢
  generalize T' ^ k = D at h4 ⊢
  generalize g ^ N = E at h h5 ⊢
  generalize ka ^ N = F at h h6 ⊢
  field_simp at h ⊢
  linear_combination h

end Formalism.HermitianLatticeCounting.P
