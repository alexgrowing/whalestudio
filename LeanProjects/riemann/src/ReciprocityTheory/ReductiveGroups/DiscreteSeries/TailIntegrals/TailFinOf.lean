import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.CriticalExponentSucc

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi

namespace J2

lemma sum_Iic {n : ℕ} (g : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∑ j ∈ Finset.Iic l, g j = ∑ j, if j ≤ l then g j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

lemma sum_Ioi {n : ℕ} (g : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∑ j ∈ Finset.Ioi l, g j = ∑ j, if l < j then g j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

lemma iic_zero {n : ℕ} (g : Fin (n + 1) → ℝ) : ∑ j ∈ Finset.Iic 0, g j = g 0 := by
  rw [sum_Iic]
  simp [Fin.le_zero_iff]

lemma upd_eq {p : ℕ} (ν : Fin (p + 2) → ℝ) :
    Function.update (Fin.tail ν) 0 (ν 0 + Fin.tail ν 0) = fun j => ν j.succ + if j = 0 then ν 0 else 0 := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [Fin.tail, add_comm]
  · simp [Fin.tail]

lemma iic_succ {p : ℕ} (ν : Fin (p + 2) → ℝ) (l : Fin (p + 1)) :
    ∑ j ∈ Finset.Iic l.succ, ν j = ν 0 + ∑ j ∈ Finset.Iic l, ν j.succ := by
  rw [sum_Iic, sum_Iic (fun j => ν j.succ), Fin.sum_univ_succ (n := p + 1)]
  simp [Fin.succ_le_succ_iff]

lemma ioi_succ {p : ℕ} (ν : Fin (p + 2) → ℝ) (l : Fin (p + 1)) :
    ∑ j ∈ Finset.Ioi l.succ, ν j = ∑ j ∈ Finset.Ioi l, ν j.succ := by
  rw [sum_Ioi, sum_Ioi (fun j => ν j.succ), Fin.sum_univ_succ (n := p + 1)]
  simp [Fin.succ_lt_succ_iff]

lemma cond_step {p : ℕ} (ν : Fin (p + 2) → ℝ) (h : CHCond (p + 1) ν) :
    0 < ν 0 ∧ 0 < ν 0 + 2 * ∑ i, Fin.tail ν i ∧
      CHCond p (Function.update (Fin.tail ν) 0 (ν 0 + Fin.tail ν 0)) := by
  obtain ⟨h1, h2⟩ := h
  have hI : ∑ j ∈ Finset.Ioi (0 : Fin (p + 2)), ν j = ∑ i, Fin.tail ν i := by
    rw [sum_Ioi, Fin.sum_univ_succ (n := p + 1)]
    simp [Fin.tail, Fin.succ_pos]
  have e0 := h1 0
  rw [iic_zero] at e0
  refine ⟨e0, ?_, ?_⟩
  · have := h2 0 (by simp)
    rw [iic_zero, hI] at this
    exact this
  · rw [upd_eq]
    have hA : ∀ l : Fin (p + 1), ∑ j ∈ Finset.Iic l, (ν j.succ + if j = 0 then ν 0 else 0) =
        ∑ j ∈ Finset.Iic l.succ, ν j := by
      intro l
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_Iic.2 (Fin.zero_le l)),
        iic_succ]
      ring
    have hB : ∀ l : Fin (p + 1), ∑ j ∈ Finset.Ioi l, (ν j.succ + if j = 0 then ν 0 else 0) =
        ∑ j ∈ Finset.Ioi l.succ, ν j := by
      intro l
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_neg (by simp), ioi_succ, add_zero]
    refine ⟨fun l => ?_, fun l hl => ?_⟩
    · beta_reduce
      rw [hA]
      exact h1 l.succ
    · beta_reduce
      rw [hA, hB]
      exact h2 l.succ (by rw [Fin.val_succ]; omega)

end J2

theorem c1 : C1 := by
  intro p m x
  rw [J2.de_sq, J2.de_sq, J2.lsq_zero, J2.rhoSq_zero, J2.bco_zero, J2.lsq_one]
  have hL : (0 : ℝ) < 1 + ((x.1 0).re * (x.1 0).re + (x.1 0).im * (x.1 0).im) := by
    nlinarith [mul_self_nonneg (x.1 0).re, mul_self_nonneg (x.1 0).im]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im]
  field_simp
  ring

theorem tailFin_of (hCH : CH) : TailFin := by
  intro p m α ν hc hpos
  rw [J2.tail_eq]
  exact ENNReal.mul_lt_top (J2.kc_lt_top (by linarith)) (hCH p m _ hc)

theorem ch_of (hC1 : C1) : CH := by
  intro p
  induction p with
  | zero =>
    intro m ν hν
    exact J2.ch_base m ν (by have := hν.1 0; rwa [J2.iic_zero] at this)
  | succ p ih =>
    intro m ν hν
    obtain ⟨h0, hs, hc⟩ := J2.cond_step ν hν
    rw [J2.ch_step, J2.tail_eq]
    exact ENNReal.mul_lt_top (J2.kc_lt_top (by linarith))
      (ENNReal.mul_lt_top (J2.kc_lt_top (by linarith)) (ih m _ hc))

end ReciprocityTheory.ChartRestriction.DS.Xi
