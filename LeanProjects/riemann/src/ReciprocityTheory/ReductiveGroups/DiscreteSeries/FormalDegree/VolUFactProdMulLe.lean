import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def volU (M : ℕ) : ℝ := ∏ i ∈ range M, 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)

theorem volU_eq_pow_div (M : ℕ) : volU M = 2 ^ M * Real.pi ^ (∑ i ∈ range M, (i + 1)) /
    ∏ i ∈ range M, (i.factorial : ℝ) := by
  rw [volU, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Finset.prod_pow_eq_pow_sum]

theorem volU_sum_succ_add (p q : ℕ) : ∑ i ∈ range (p + q), (i + 1) =
    ∑ i ∈ range p, (i + 1) + ∑ i ∈ range q, (i + 1) + p * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← Nat.add_assoc, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

theorem volU_factProd_pos (M : ℕ) : (0 : ℝ) < ∏ i ∈ range M, (i.factorial : ℝ) := Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos i)

theorem volU_ratio (p q m : ℕ) (h : p + q = m) :
    volU p * volU q / volU m = (∏ i ∈ range m, (i.factorial : ℝ)) /
      (Real.pi ^ (p * q) * (∏ i ∈ range p, (i.factorial : ℝ)) *
        ∏ i ∈ range q, (i.factorial : ℝ)) := by
  subst h
  have hp := volU_factProd_pos p
  have hq := volU_factProd_pos q
  have hn := volU_factProd_pos (p + q)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [volU_eq_pow_div, volU_eq_pow_div, volU_eq_pow_div, volU_sum_succ_add]
  simp only [pow_add]
  field_simp

theorem volU_factProd_mul_le (p q : ℕ) :
    (∏ i ∈ range p, i.factorial) * (∏ i ∈ range q, i.factorial) ≤
      ∏ i ∈ range (p + q), i.factorial := by
  rw [Finset.prod_range_add]
  exact Nat.mul_le_mul le_rfl
    (Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => Nat.factorial_le (by omega)))

theorem volU_pOf_add_qOf (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  unfold pOf qOf
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have hone : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem cPQ_eq_volU (ε : Fin n → Bool) : cPQ ε = volU (pOf ε) * volU (qOf ε) / volU n := by
  rw [volU_ratio _ _ _ (volU_pOf_add_qOf ε)]
  rfl

theorem inv_pi_pow_le_cPQ (ε : Fin n → Bool) : (Real.pi ^ (pOf ε * qOf ε))⁻¹ ≤ cPQ ε := by
  have hle := volU_factProd_mul_le (pOf ε) (qOf ε)
  rw [volU_pOf_add_qOf ε] at hle
  have hle' : (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) ≤
      ∏ i ∈ range n, (i.factorial : ℝ) := by
    exact_mod_cast hle
  have hp := volU_factProd_pos (pOf ε)
  have hq := volU_factProd_pos (qOf ε)
  have hpi : 0 < Real.pi ^ (pOf ε * qOf ε) := pow_pos Real.pi_pos _
  have hD : 0 < Real.pi ^ (pOf ε * qOf ε) * (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) *
      ∏ i ∈ range (qOf ε), (i.factorial : ℝ) := mul_pos (mul_pos hpi hp) hq
  unfold cPQ
  rw [le_div_iff₀ hD]
  have he : (Real.pi ^ (pOf ε * qOf ε))⁻¹ * (Real.pi ^ (pOf ε * qOf ε) *
      (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ)) =
      (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) := by
    rw [mul_assoc, inv_mul_cancel_left₀ hpi.ne']
  linarith

end ReciprocityTheory.ChartRestriction.DS
